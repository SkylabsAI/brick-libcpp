Require Import bluerock.auto.cpp.hints.prelude.

Require Import bluerock.prelude.telescopes.
Require Import bluerock.iris.extra.bi.telescopes.

Require Import bluerock.lang.cpp.logic.dispatch.
Require Import bluerock.auto.cpp.definitions.
Require Import bluerock.auto.cpp.specifications.

Require Import bluerock.auto.cpp.hints.invoke.
Require Import bluerock.auto.cpp.hints.alignment.
Require Import bluerock.auto.cpp.hints.prim.
Require Import bluerock.auto.cpp.hints.sizeof.

Require Export bluerock.cpp.virtual.

Import linearity.


Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Context (ρ : region).

  #[local] Set Universe Polymorphism.
  #[local] Open Scope free_scope.

  Notation wp_prval := (wp_prval tu ρ).
  Notation wp_operand := (wp_operand tu ρ).
  Notation wp_lval := (wp_lval tu ρ).
  Notation wp_xval := (wp_xval tu ρ).
  Notation wp_glval := (wp_glval tu ρ).
  Notation wp_init := (wp_init tu ρ).
  Notation wp_initialize := (wp_initialize tu ρ).


  Theorem wp_operand_array_new_glob_unsound :
    forall (array_size : Expr) (oinit : option Expr)
      new_fn (pass_align : bool) new_args new_targs aty Q targs
      (nfty := normalize_type new_fn.2)
      (_ : args_for <$> as_function nfty = Some targs),
      args_for <$> as_function new_fn.2 = Some new_targs ->
      (letI* v, free := wp_operand array_size in
        Exists array_sizeN, [| v = Vn array_sizeN |] **
          (* The size must be non-negative. *)
          [| 0 <= array_sizeN |]%N **
          Exists alloc_sz alloc_al,
          let array_ty := Tarray aty array_sizeN in
          [| size_of _ array_ty = Some alloc_sz |] **
          [| align_of aty = Some alloc_al |] ** (** <-- TODO FM-975 *)
          [| has_type_prop alloc_sz Tsize_t |] **
         (*  (Q (Vptr nullptr) free //\\ *)(
            (* ^^ handles when the overhead exceeds the size? when does that happen? how can a user guarantee that doesnt happen: it seems the LHS of //\\ needs to be tightened *)
          Forall overhead_sz : N,
            [| has_type_prop (overhead_sz + alloc_sz)%N Tsize_t |] -*
            let implicit_args :=
                new_implicits pass_align (overhead_sz + alloc_sz) alloc_al in
          letI* _, args, vargs, free :=
              wp_unmaterialized_args tu ρ evaluation_order.nd [] new_targs (implicit_args ++ new_args) in
          letI* res := wp_invoke_O tu new_fn.2 (inl $ Vptr $ _global new_fn.1) args vargs in
          match res with
          | Vptr storage_base =>
              if bool_decide (storage_base = nullptr) then
                Q (Vptr storage_base) free
              else
                let storage_ptr := storage_base .[ Tbyte ! overhead_sz ] in
                (* [blockR alloc_sz -|- tblockR (Tarray aty array_size)] *)
                storage_base |-> blockR (overhead_sz + alloc_sz) 1$m **
                storage_base |-> alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                  (Forall (obj_ptr : ptr),
                    storage_ptr |-> alignedR alloc_al -*

                    (* This also ensures these pointers share their
                    address (see [provides_storage_same_address]) *)
                    provides_storage storage_ptr obj_ptr array_ty -*
                    letI* free'' :=
                        match oinit with
                        | Some init => wp_initialize array_ty obj_ptr init
                        | None => default_initialize tu array_ty obj_ptr
                        end
                      in
                      (* Track the type we are allocating
                        so it can be checked at [delete]
                      *)
                      obj_ptr |-> new_token.R 1 (new_token.mk array_ty storage_ptr overhead_sz) -*
                      Q (Vptr obj_ptr) (free'' >*> free))
          | _ => False
          end))
  |-- wp_operand (Enew new_fn new_args (new_form.Allocating pass_align) aty (Some array_size) oinit) Q.
  Proof.
  Admitted.

  Definition wp_operand_array_new_glob_unsound_B := [BWD] wp_operand_array_new_glob_unsound.


End with_Σ.

(** import this file only when you want your proofs to ignore the case when dynamic allocation fails (typically due to memory insufficiency) *)
#[global] Hint Resolve
 wp_operand_array_new_glob_unsound_B | 150 : db_bluerock_wp.
