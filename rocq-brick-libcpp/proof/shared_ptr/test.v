Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.stdlib.allocator.spec.
Require Import bluerock.cpp.stdlib.cassert.spec.
Require Import bluerock.cpp.stdlib.vector.spec.
Require Import bluerock.cpp.stdlib.atomic.spec.
Require Import bluerock.cpp.stdlib.algorithms.spec.
Require Import bluerock.cpp.stdlib.new.spec_exc.
Require Import bluerock.brick.libcpp.newarr.spec_exc.
Require Import bluerock.brick.libcpp.newarr.hints.
Require Import bluerock.brick.libcpp.newarr.test. (* TODO move [dynAllocatedR] to a non-test file *)
Require Import bluerock.cpp.spec.concepts.
Require Import bluerock.cpp.spec.concepts.experimental.
Require Import bluerock.brick.libcpp.shared_ptr.test_cpp.
Require Import bluerock.brick.libcpp.shared_ptr.specs.


(* TODO: upstream the hints/lemmas, to where? *)
Hint Resolve NoDup_seq : setsolver.
Hint Rewrite elem_of_seq: equiv.
Hint Rewrite @big_sepL_emp: equiv.

Lemma seqprefix (prelen len start: nat):
  (prelen <= len)%nat -> seq start len = (seq start prelen)++(seq (start+prelen) (len -prelen)).
Proof using.
  intros Hl.
  replace len with (prelen+(len-prelen))%nat at 1 by lia.
  rewrite seq_app.
  reflexivity.
Qed.
  
Lemma one_as_bigsep {PROP: bi} {A} {eqd: EqDecision A} (f  : PROP) l (x: A):
  x ∈ l ->
  NoDup l -> (* too strong: we only need x to be not duplicated *)
  f -|- ([∗ list] id ∈ l, if bool_decide (id=x) then f else emp)%I.
Proof using.
  intros.
  rewrite  -> big_op.big_sepL_difference_singleton with (x:=x) by assumption.
  simpl.
  case_bool_decide; [ | congruence].
  assert (f ** (emp)%I ≡ f) as Heq by (apply right_id; eauto with typeclass_instances).
  rewrite <- Heq at 1.
  f_equiv.
  rewrite <- big_sepL_emp with (l:=(list_difference l [x])).
  apply big_opL_proper.
  intros  ? id  Hl.
  case_decide;[ | reflexivity].
  subst.
  apply elem_of_list_lookup_2 in Hl.
  apply elem_of_list_difference in Hl.
  forward_reason.
  apply False_rect.
  simpl in *.
  set_solver.
Qed.

Section proofs.
  Opaque SharedPtrR.
  Context `{Σ : cpp_logic, MOD:test_cpp.module ⊧ σ}
  {hf:fracG () _Σ}.
  
  Definition observeSharedType r q t Rpiece op:= @observe_fwd _ _ _ (sharedR_typeptr_observe r q t Rpiece op).

  cpp.spec "testshared1()" as testshared1spec with (
    \pre emp
    \post{p:ptr}[Vptr p] Exists payload sid,
       p |-> SharedPtrR "int" sid (fun ctid => if bool_decide (ctid=0%nat) then anyR "int" 1 else emp) payload
       ** payload |-> intR (cQp.m 1) 1
       ** ([∗ list] ctid ∈ allButFirstPieceId,
              pieceRight sid ctid)
    ).



  Lemma allButFirstEmp ty : ([∗ list] x ∈ seq 1 (Pos.to_nat maxContention -1), 
       if bool_decide (x = 0%nat)
       then anyR ty 1$m
       else emp)
                         -|- emp.
  Proof using.
    erewrite  big_opL_proper with (g := fun _ _=> emp).
    2:{ intros ? ? Hl.
        apply elem_of_list_lookup_2 in Hl.
        autorewrite with equiv in Hl.
        resolveDecide lia.
        reflexivity.
    }
    autorewrite with equiv.
    reflexivity.
  Qed.
  
  Opaque NullSharedPtrR.
  Hint Resolve observeSharedType : br_opacity.
  
  Lemma prf2: verify[module] testshared1spec.
  Proof using MOD.
    verify_spec.
    pose proof maxContentionLb.
    go.
    unfold dynAllocatedR.
    iExists _.
    set (Rpiece:=(fun ctid => if bool_decide (ctid=0%nat) then anyR "int" 1 else emp)).
    iExists Rpiece.
    go.
    iExists _.
    simpl.
    eagerUnifyU.
    go.
    normalize_ptrs.
    eagerUnifyU.
    go.
    rewrite <- _at_big_sepL.
    unfold allButFirstPieceId.
    unfold Rpiece.
    rewrite allButFirstEmp. go.
    provePure.
    {
      unfold allPieceIds.
      rewrite -> seqprefix with (prelen:=1%nat) by lia.
      simpl.
      rewrite allButFirstEmp. go.
    }
    go.
    go.
    iExists _, _, Rpiece.
    unfold upcast_offset.
    normalize_ptrs.
    eagerUnifyU.
    go.
    normalize_ptrs.
    go.
    iExists _, _, Rpiece.
    eagerUnifyU.
    go.
    iExists true.
    iExists nullptr.
    iExists tt.
    iExists Rpiece.
    ego.
  Qed.
End proofs.
