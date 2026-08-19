(**
 * Copyright (C) 2025 SkyLabs AI, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.atomic.spec.
(* Require Import skylabs.brick.libstdcpp.test.atomic.test_cpp. *)
Require Import skylabs.brick.libstdcpp.atomic.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Abbreviation GLOBALS q := (_global "std::memory_order_seq_cst" |-> primR "enum std::memory_order" q 5).

  Section specs.
    Context `{MOD : test_cpp.source ⊧ σ}.

    cpp.spec "test(bool, const char*)" as test_spec with
      (\arg "b" (Vbool true)
       \arg{p} "" (Vptr p)
       \post emp).

    cpp.spec "TestDefaultConstructor()" as test_default_ctor with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "TestParameterizedConstructor()" as test_parameterized_ctor with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "TestLoad()" as test_load with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "TestStore()" as test_store with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "TestCAS()" as test_cas with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "TestArith()" as test_arith with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "TestFetchAdd()" as test_fetch_add with
        (\prepost{q} GLOBALS q
         \post emp).

    cpp.spec "main()" as main with
        (\prepost{q} GLOBALS q
         \post[Vint 0] emp).

    Definition specs :=
      test_default_ctor **
      test_parameterized_ctor **
      test_load **
      test_store **
      test_cas **
      test_arith.
    #[global] Hint Opaque specs : sl_opacity.

  End specs.

  #[local] Hint Resolve fractional.UNSAFE_read_prim_cancel : sl_opacity.

  Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

  Ltac normalize_ptrs := idtac.
  #[program]
  Definition do_load_C (p : ptr) :=
    \cancelx
    \using denoteModule test_cpp.source
    \consuming{q (n : Z)} p |-> atomic.R "int" q n
    \proving{(K : Z -> mpred) (_ : IsExistential K)} do_load Tint (BASE p) K
    \instantiate K := (fun x : Z => p |-> atomic.R "int" q n ** [| x = n |])
    \end@{mpredI}.
  Next Obligation.
    intros. iIntros "[#M ?]" (?? ->).
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    rewrite /do_load.
    iAcIntro. rewrite /commit_acc.
    iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
    work; normalize_ptrs.
    work. iExists q. work.
    iMod "Y". iModIntro.
    normalize_ptrs. work.
  Qed.
  #[program]
  Definition do_store_C (p : ptr) :=
    \cancelx
    \using denoteModule test_cpp.source
    \consuming{(n : Z)} p |-> atomic.R "int" 1$m n
    \proving{K (_ : IsExistential K) v} do_store Tint (BASE p) v K
    \instantiate K := (p |-> atomic.R "int" 1$m v)
    \end@{mpredI}.
  Next Obligation.
    intros. iIntros "[#M ?]" (??? ->).
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    rewrite /do_load.
    iAcIntro. rewrite /commit_acc.
    iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
    work; normalize_ptrs.
    work.
    iMod "Y". iModIntro.
    normalize_ptrs. work.
  Qed.
  (* TODO: this is not the most general hint *)
  #[program]
  Definition do_compare_exchange_C (p p' : ptr) old new :=
    \cancelx
    \using (denoteModule test_cpp.source : mpred)
    \consuming{n} p |-> atomic.R "int" 1$m (n : Z)
    \proving{K (_ : IsExistential K)}
      do_compare_exchange "int" false (BASE p) p' old new K
    \instantiate K := (fun res =>
                         if bool_decide (n = old) then
                           p |-> atomic.R "int" 1$m new **
                           p' |-> primR "int" 1$m old ** [| res = true |]
                         else
                           p |-> atomic.R "int" 1$m n **
                           p' |-> primR "int" 1$m n ** [| res = false |])
    \end@{mpredI}.
  Next Obligation.
    intros. iIntros "[#M ?]" (?? ->).
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    rewrite /do_compare_exchange.
    iAuIntro1. rewrite /atomic1_acc.
    iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
    work. normalize_ptrs. work.
    { iMod "Y". iModIntro. normalize_ptrs. work. }
    { iMod "Y"; iModIntro. normalize_ptrs. work.
      case_bool_decide.
      { subst. lazymatch goal with H : _ \/ _ |- _ => destruct H end. intuition. work.
        exfalso; tauto. }
      { lazymatch goal with H : _ \/ _ |- _ => destruct H end; try by exfalso; tauto.
        intuition; subst. work. } }
  Qed.
  #[program]
  Definition do_exchange_C (p : ptr) new :=
    \cancelx
    \using denoteModule test_cpp.source
    \consuming{n} p |-> atomic.R "int" 1$m n
    \proving{K (_ : IsExistential K)}
      do_exchange "int" (BASE p) new K
    \instantiate K := (fun res => [| res = n |] **
                         p |-> atomic.R "int" 1$m new)
    \end@{mpredI}.
  Next Obligation.
    intros. iIntros "[#M ?]" (?? ->).
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    rewrite /do_compare_exchange.
    iAuIntro1. rewrite /atomic1_acc.
    iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
    work. normalize_ptrs. work.
    { iMod "Y". iModIntro. normalize_ptrs. work. }
    { iMod "Y"; iModIntro. normalize_ptrs. work. }
  Qed.

  #[program]
  Definition do_op_C (p : ptr) (op : Z -> Z) :=
    \cancelx
    \using denoteModule test_cpp.source
    \consuming{n} p |-> atomic.R "int" 1$m n
    \proving{K (_ : IsExistential K)}
      spec.do_op "int" op (BASE p) K
    \instantiate K := (fun res => [| res = n |] **
                               p |-> atomic.R "int" 1$m (op n))
    \end@{mpredI}.
  Next Obligation.
    intros. iIntros "[#M ?]" (?? ->).
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    rewrite /spec.do_op.
    iAcIntro. rewrite /commit_acc.
    iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
    work.
    iMod "Y"; iModIntro; work.
  Qed.

  Hint Resolve do_compare_exchange_C do_exchange_C : sl_opacity.
  Hint Resolve do_load_C do_store_C : sl_opacity.
  Hint Resolve do_op_C : sl_opacity.

  Abbreviation OK spec :=
    (verify?[test_cpp.source] spec) (only parsing).

  Set Typeclasses Debug.
  Goal SpecFor source "std::__1::atomic<int*>::fetch_add(long, enum std::__1::memory_order)"%cpp_name.
  Fail apply _.
  About SpecFor_fetch_binop.
  Check (SpecFor_fetch_binop "int*").
  class_apply (SpecFor_fetch_binop "int*").
  Goal SpecFor source "std::__1::__atomic_base<int, 1b>::operator++(int)".
  apply _.

  Lemma arith_ok : OK test_fetch_add.
  Proof. verify_spec. go.

  Qed.

  Lemma cas_ok : OK test_cas.
  Proof. verify_spec. go. Qed.

  Lemma default_ctor_ok : OK test_default_ctor.
  Proof. verify_spec; go. Qed.

  Lemma param_ctor_ok : OK test_parameterized_ctor.
  Proof. verify_spec; go. Qed.

  Lemma load_ok : OK test_load.
  Proof. verify_spec; go. Qed.

  Lemma store_ok : OK test_store.
  Proof. verify_spec; go. Qed.

  Lemma main_ok : OK main.
  Proof.
    rewrite /specs.
    verify_spec. go.
  Qed.

End with_cpp.
