(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.lib.tactics.
Require Import skylabs.brick.libstdcpp.test.vector.test_cpp.

Require Import skylabs.auto.cpp.prelude.test.

Module Aggregate.
  Import concepts.

   cpp.class "Aggregate" prefix "" from source
    dataclass { copyable ; movable ; destructible }.
  #[only(eq_dec)] derive T.

  (* this could be generated *)
  #[global] Instance BundledRep_Aggregate `{Σ : cpp_logic, σ : genv} :
    BundledRep "Aggregate" T := {| objR := R |}.

  (* this could be generated *)
  #[global] Instance DefaultValue_Aggregate `{Σ : cpp_logic, σ : genv} :
    DefaultValue "Aggregate" T :=
    {| default_val :=
        {| x := default_val "int";
           y := default_val "int";
           z := default_val "int";|} |}.

  (* this could be generated *)
  #[global] Instance MovedValue_Aggregate `{Σ : cpp_logic, σ : genv} :
    MovedValue "Aggregate" T :=
    {| moved :=
        fun a a' =>
          moved "int" (x a) (x a') ∧
          moved "int" (y a) (y a') ∧
          moved "int" (z a) (z a') |}.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.
    Section specs.
      Context `{MOD : test_cpp.source ⊧ σ}.

      cpp.spec "Aggregate::Aggregate(int)" as ctor_spec with
          (\this this
           \arg{a} "a" (Vint a)
           \let r := {| Aggregate.x := a; Aggregate.y := a ; Aggregate.z := a |}
           \post this |-> Aggregate.R 1$m r ).

      cpp.spec "Aggregate::operator==(Aggregate&)" as op_eq_spec with
          (\this this
           \arg{otherp} "otherp" (Vptr otherp)
           \prepost{qa a}  this |-> R qa a
           \prepost{qb b}  otherp |-> R qb b
           \post[Vbool (bool_decide (a = b))] emp ).

      cpp.spec "Aggregate::operator!=(Aggregate&)" as op_neq_spec with
          (\this this
           \arg{otherp} "otherp" (Vptr otherp)
           \prepost{qa a}  this |-> R qa a
           \prepost{qb b}  otherp |-> R qb b
           \post[Vbool (bool_decide (a ≠ b))] emp ).

      Definition specs :=
        ctor_spec **
        copy_ctor_spec **
        copy_assign_spec **
        move_ctor_spec **
        move_assign_spec **
        op_eq_spec **
        op_neq_spec **
        dtor_spec .

    End specs.

    Section proofs.
      Context `{MOD : test_cpp.source ⊧ σ}.
      Import linearity.

      Lemma copy_ctor_ok :
        denoteModule source |-- copy_ctor_spec.
      Proof using MOD. verify_spec. go. Qed.
      Definition copy_ctor_B := [LINK] copy_ctor_ok.

      Lemma move_ctor_ok :
        denoteModule source |-- move_ctor_spec.
      Proof using MOD. verify_spec. go. Qed.
      Definition move_ctor_B := [LINK] move_ctor_ok.

      Lemma ctor_ok :
        denoteModule source |-- ctor_spec.
      Proof using MOD. verify_spec. go. Qed.
      Definition ctor_B := [LINK] ctor_ok.

      Lemma dtor_ok :
        denoteModule source |-- dtor_spec.
      Proof using MOD. verify_spec. go. Qed.
      Definition dtor_B := [LINK] dtor_ok.

      Import join.manual_expr_condition.
      Import reduce_bool_decide.

      Lemma iff_eqv_both_or_neither {P Q : Prop} `{HdecP : !Decision P} :
        (P <-> Q) <-> (P ∧ Q) ∨ (¬ P ∧ ¬ Q).
      Proof.
        split.
        - by move => <-; case: HdecP; [left|right].
        - by move => [] [HP HQ].
      Qed.

      Lemma op_eq_ok :
        denoteModule source |-- op_eq_spec.
      Proof using MOD.
        verify_spec.
        case: (bool_decide_reflect (a = b)) => Hab.
        - go using prim.primR_aggressiveC with smash_delayed_case.
          by [].
        - go with smash_delayed_case; iIntros "!%".
          + rewrite iff_eqv_both_or_neither; right; split; last by [].
            move => Hzab.
            apply: Hab; by destruct a, b; f_equal.
          + by rewrite iff_eqv_both_or_neither; right; split => +.
          + by rewrite iff_eqv_both_or_neither; right; split => +.
      Qed.
      Definition op_eq_B := [LINK] op_eq_ok.

      Lemma op_neq_ok :
        denoteModule source |-- op_neq_spec.
      Proof using MOD.
        verify_spec. wapply op_eq_ok.
        go using prim.primR_aggressiveC.
        by [].
      Qed.
      Definition op_neq_B := [LINK] op_neq_ok.

    End proofs.
  End with_cpp.
End Aggregate.

#[local] Hint Resolve Aggregate.ctor_B : sl_opacity.
#[local] Hint Resolve Aggregate.dtor_B : sl_opacity.
#[local] Hint Resolve Aggregate.op_eq_B : sl_opacity.
#[local] Hint Resolve Aggregate.op_neq_B : sl_opacity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Section defs.

    Definition sum (xs : list Z) : Z :=
      foldr Z.add 0 xs.
    #[global] Arguments sum !_ / : simpl nomatch.

  End defs.

  Section specs.
    Context `{MOD : test_cpp.source ⊧ σ}.

    cpp.spec "test(bool, const char* )" as test_spec with
      (\arg "b" (Vbool true)
       \arg{p} "" (Vptr p)
       \post emp).

    cpp.spec "sum(const std::vector<unsigned int, std::allocator<unsigned int>>&)" as sum_spec with
        ( \arg{vp} "v" (Vptr vp)
          \with q vs st size
          \prepost vp |-> std.vector.R_cap "unsigned" q size st vs
          \post[Vint (trim 32 (sum vs))] emp).

    cpp.spec "TestBasic()" as test_basic with
        (\post emp).

    cpp.spec "TestIntIter()" as test_int_iter with
        (\post emp).

    cpp.spec "TestForEach()" as test_for_each with
        (\post emp).

    cpp.spec "TestAllocCtor()" as test_alloc_ctor with
        (\post emp).

    cpp.spec "TestAggregate()" as test_aggregate with
        (\post emp).

    cpp.spec "main()" as main with
        (\post[Vint 0] emp).

    Definition specs :=
      test_basic **
        main.
  End specs.

  Section proofs.
    Context `{MOD : test_cpp.source ⊧ σ}.
    #[local] Abbreviation alloc_int := (std.allocator.T "int").
    #[local] Abbreviation alloc_uint := (std.allocator.T "unsigned").
    #[local] Abbreviation alloc_agg := (std.allocator.T "Aggregate").
    Implicit Type p : ptr.

    Import linearity.
    Import normalize.normalize_ptr normalize.only_provable_norm.

    Lemma test_int_iter_ok : verify[ source ] test_int_iter.
    Proof using MOD.
      verify_spec.
      time "test_int_iter_ok" go.
    Qed.
    Definition test_int_iter_B := [LINK] test_int_iter_ok.
    #[local] Hint Resolve test_int_iter_B : sl_opacity.

    #[local] Hint Resolve prim.primR_aggressiveC : sl_opacity.

    Lemma test_for_each_ok : verify[ source ] test_for_each.
    Proof using MOD.
      verify_spec.
      time "test_for_each_ok" go.
    Qed.
    Definition test_for_each_B := [LINK] test_for_each_ok.
    #[local] Hint Resolve test_for_each_B : sl_opacity.

    Lemma sum_ok : verify[ source ] sum_spec.
    Proof using MOD.
      verify_spec.
      time "test_for_each_ok" go.

      name_locals; rename
        __begin1_addr into beginp,
        __end1_addr   into endp.

      wp_for (fun _ =>
        \with basep
        \pre{ib}     beginp |-> std.vector.iterator.R_const "unsigned" 1$m basep ib
        \prepost{ie} endp   |-> std.vector.iterator.R_const "unsigned" 1$m basep ie
        \prepost{vs} basep |-> array_sliceR "unsigned" ib ie (fun v => uintR q v) vs
        \pre{r} r_addr |-> uintR 1$m r
        \post
           r_addr |-> uintR 1$m (trim 32 (r + sum vs)) ∗
           beginp |-> std.vector.iterator.R_const "unsigned" 1$m basep ie ).

      go; wp_if.
      { go. }
      go.
    Qed.
    Definition sum_B := [LINK] sum_ok.
    #[local] Hint Resolve sum_B : sl_opacity.

    Lemma test_basic_ok : verify[ source ] test_basic.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_basic_B := [LINK] test_basic_ok.
    #[local] Hint Resolve test_basic_B : sl_opacity.

    Lemma test_alloc_ctor_ok : verify[ source ] test_alloc_ctor.
    Proof using MOD.
      verify_spec.
      go.
      iExists (). iFrame. iIntros "?". go.
    Qed.
    Definition test_alloc_ctor_B := [LINK] test_alloc_ctor_ok.
    #[local] Hint Resolve test_alloc_ctor_B : sl_opacity.

    Lemma test_aggregate_ok : verify[ source ] test_aggregate.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_aggregate_B := [LINK] test_aggregate_ok.
    #[local] Hint Resolve test_aggregate_B : sl_opacity.

    Lemma test_ok : verify[ source ] test_spec.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_B := [LINK] test_ok.
    #[local] Hint Resolve test_B : sl_opacity.

    Lemma main_ok : verify[ source ] main.
    Proof using MOD.
      verify_spec.
      go.
    Qed.

    Definition main_B := [LINK] main_ok.
    #[local] Hint Resolve main_B : sl_opacity.

    (* glue all the proofs together *)
    Lemma specs_ok :
      denoteModule source **
      ▷ ( std.vector.specs "Aggregate" alloc_agg **
          std.vector.specs "int" alloc_int **
          std.vector.specs "unsigned" alloc_uint **
          std.vector.iterator.specs true "unsigned" alloc_uint **
          std.vector.iterator.specs false "int" alloc_int **
          std.find_spec (std.vector.iterator.T "int") "int" source **
          std.allocator.specs "int" **
          std.cassert.specs)
      |-- main.
    Proof using MOD.
      rewrite /std.vector.specs.
      rewrite /std.vector.iterator.specs.
      rewrite /std.cassert.specs.
      rewrite /std.allocator.specs.
      work.
    Qed.

  End proofs.
End with_cpp.
