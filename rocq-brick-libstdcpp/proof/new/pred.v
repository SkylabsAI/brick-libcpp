Require Import bluerock.auto.cpp.prelude.pred.

Require Import bluerock.brick.libstdcpp.new.inc_new_cpp.
#[local] Set Primitive Projections.

cpp.enum "std::align_val_t" from module alias.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** The allocation meta-data **owned by the allocator**.

      In a normal implementation of <<malloc>>, this is a few bytes before the
      returned pointer that stores meta data, e.g. the size of the allocation.

      NOTE: While C++ often stores the size of the array next to a dynamically
      allocated array, the memory that backs this is **not** part of [allocatedR].
      That memory is owned by the C++ abstract machine.
   *)
  Parameter allocatedR : forall {σ : genv}, Qp -> N -> Rep.
  #[global] Instance: Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) allocatedR).
  Proof. solve_learnable. Qed.

End with_cpp.

(* TODO: upstream this! *)
Class IsNotArray (ty : type) : Prop :=
  { _ : if ty is Tarray _ _ then False else True }.
#[global] Hint Extern 0 (IsNotArray _) => (constructor; exact I) : typeclass_instances.

(* TODO: upstream this! *)
(** This guarantees that non-array allocations have 0 overhead bytes. *)
#[global] Declare Instance new_token_non_array_0_overhead : forall `{Σ : cpp_logic} {σ : genv} ty q storage_p overhead,
    IsNotArray ty ->
    Observe [| overhead = 0%N |] (new_token.R q $ new_token.mk ty storage_p overhead).

NES.Begin alloc.

  (** [token ty sz q] bundles the dynamic allocation tokens provided by
      the C++ abstract machine with the [allocatedR] fact from the allocation library.
   *)
  br.lock
  Definition token `{Σ : cpp_logic} {σ : genv} (ty : type) (q : Qp) : Rep :=
    Exists storage_p overhead sz,
      [| size_of _ ty = Some sz |] **
      new_token.R q {| new_token.alloc_ty := ty ; new_token.storage_ptr := storage_p ; new_token.overhead := overhead |} **
      pureR (storage_p .[ "unsigned char" ! -overhead ] |-> allocatedR q (overhead + sz)).

NES.End alloc.
