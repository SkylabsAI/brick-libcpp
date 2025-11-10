Require Import iris.proofmode.tactics.
Require Import bluerock.auto.cpp.prelude.pred.
Require Import bluerock.auto.cpp.elpi.derive.bi.
Require Import bluerock.brick.libstdcpp.new.inc_new_cpp.
#[local] Set Primitive Projections.

cpp.enum "std::align_val_t" from module alias.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** The ownership of the allocator data structures.

   This would include ownership such as free lists and allocator data structures.
   In C++, these are generally ambient, so this is exposed as a predicate
   rather than a representation predicate.

   NOTE/TODO: The current interface does **not** expose a global predicate for
   the ownership of the allocator because doing so would effectively require
   threading this ownership everywhere which is not very ergonomic; however,
   formally, this makes the interface un-realizable.

   More investigation is needed to understand how to encapsulate this ownership
   (and other ownership like it). The most promising option to date is to use
   thread-local invariants, but this still introduces some level of verbosity.
   *)
  Parameter allocatorP : forall {σ : genv}, Qp -> mpred.
  #[only(fractional,fracvalid)] derive allocatorP.

  (** The allocation meta-data **owned by the allocator**.

      In a normal implementation of <<malloc>>, this is a few bytes before the
      returned pointer that stores meta data, e.g. the size of the allocation.

      NOTE: While C++ often stores the size of the array next to a dynamically
      allocated array, the memory that backs this is **not** part of [allocatedR].
      That memory is owned by the C++ abstract machine.
   *)
  Parameter allocatedR : forall {σ : genv}, Qp -> N -> Rep.
  #[only(fractional,asfractional,fracvalid,timeless)] derive allocatedR.
  #[global] Instance: Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) allocatedR).
  Proof. solve_learnable. Qed.

End with_cpp.

NES.Begin alloc.

  (** [token ty sz q] bundles the dynamic allocation tokens provided by
      the C++ abstract machine with the [allocatedR] fact from the allocation library.
   *)
  br.lock
  Definition tokenR `{Σ : cpp_logic} {σ : genv} (ty : type) (q : Qp) : Rep :=
    Exists storage_p overhead sz,
      [| size_of _ ty = Some sz |] **
      new_token.R q {| new_token.alloc_ty := ty ; new_token.storage_ptr := storage_p ; new_token.overhead := overhead |} **
      pureR (storage_p .[ "unsigned char" ! -overhead ] |-> allocatedR q (overhead + sz)).
  #[only(fractional,fracvalid,timeless)] derive new_token.R.
  #[only(fracvalid,timeless)] derive tokenR.

  #[local] Open Scope string_scope. (* for IPM *)
  #[global] Instance tokenR_frac `{Σ : cpp_logic} {σ : genv} ty
    : Fractional (tokenR ty).
  Proof.
    rewrite tokenR.unlock.
    repeat first [ apply _
                 | apply fractional_exist; intros ].
    { apply observe_2_sep_l.
      apply observe_2_only_provable_impl.
      congruence. }
    { apply observe_2_exist; intros.
      apply observe_2_sep_r, observe_2_sep_l.
      iIntros "A B".
      iDestruct (observe_2 [| _ = _ |] with "A B") as "%".
      inversion H; eauto. }
    { do 2 (apply observe_2_exist; intros).
      apply observe_2_sep_r, observe_2_sep_l.
      iIntros "A B".
      iDestruct (observe_2 [| _ = _ |] with "A B") as "%".
      inversion H; eauto. }
  Qed.

NES.End alloc.
