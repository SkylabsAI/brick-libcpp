Require Import bluerock.auto.cpp.proof.
Require Export bluerock.brick.libstdcpp.new.spec.

#[only(lazy_unfold(global))] derive alloc.tokenR.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** ** Hints for proving [alloc.token] from [new_token.R].

     - <<_using_>> hints rely on [size_of _ ty = Some ...] to already be provable, while non
       <<using>> hints introduce this fact.
       This fact is otherwise lost because it is expressed within [alloc.token].
     - <<_0>> lemmas special case for non-array allocations which are common and ensure that
       the allocation overhead at the C++ level is 0. (Allocation overhead of the allocator-level is
       separately captured in [allocatedR].)
   *)
  #[program]
  Definition token_prove_using_C (p : ptr) q storage_p overhead ty sz
    (_ : size_of _ ty = Some sz) :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \proving p |-> alloc.tokenR ty q
    \through storage_p .[ Tbyte ! -overhead ] |-> allocatedR q (overhead + sz)
    \end.
  Next Obligation.
    rewrite alloc.tokenR.unlock. work.
  Qed.

  #[program]
  Definition token_prove_C (p : ptr) q storage_p overhead ty :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \proving p |-> alloc.tokenR ty q
    \deduce{sz} [| size_of _ ty = Some sz |]
    \through storage_p .[ Tbyte ! -overhead ] |-> allocatedR q (overhead + sz)
    \end.
  Next Obligation.
    intros; iIntros "X".
    iDestruct (observe [| exists sz, size_of _ _ = _ |] with "X") as "%".
    destruct H; simpl in *.
    rewrite alloc.tokenR.unlock. iDestruct "X" as "?"; work.
  Qed.

  (* special cases for the above two hints when the overhead is 0 *)
  #[program]
  Definition token_prove_using_0_C (p : ptr) q storage_p ty sz
    (_ : size_of _ ty = Some sz) :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p 0)
    \proving p |-> alloc.tokenR ty q
    \through storage_p |-> allocatedR q sz
    \end.
  Next Obligation.
    rewrite alloc.tokenR.unlock. work.
    normalize_ptrs. iStopProof; f_equiv. f_equiv. lia.
  Qed.

  #[program]
  Definition token_prove_0_C (p : ptr) q storage_p ty :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p 0)
    \proving p |-> alloc.tokenR ty q
    \deduce{sz} [| size_of _ ty = Some sz |]
    \through storage_p |-> allocatedR q sz
    \end.
  Next Obligation.
    intros; iIntros "X".
    iDestruct (observe [| exists sz, size_of _ _ = _ |] with "X") as "%".
    destruct H; simpl in *.
    rewrite alloc.tokenR.unlock. iDestruct "X" as "?"; work.
    normalize_ptrs. iStopProof; f_equiv; f_equiv; lia.
  Qed.


  (** ** Hints for proving [new_token.R] *)
  #[program]
  Definition token_use_non_array_C (p : ptr) ty q (_ : TCEq (is_array_type ty) false) :=
    \cancelx
    \consuming p |-> alloc.tokenR (σ:=σ) ty q
    \proving{(storage_p : ptr) overhead} p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \deduce{(storage_p' : ptr) sz} [| size_of _ ty = Some sz |]
    \deduce storage_p' |-> allocatedR q sz
    \through [| storage_p = storage_p' |]
    \through [| overhead = 0 |]%N
    \end.
  Next Obligation.
    intros.
    rewrite alloc.tokenR.unlock.
    iIntros "X"; iDestruct "X" as (????) "[X ?]".
    iDestruct (observe [| overhead = 0%N |] with "X") as "%".
    subst. normalize_ptrs.
    iExists storage_p.
    iDestruct "X" as "?".
    work.
  Qed.

  #[program]
  Definition token_use_array_C (p : ptr) ty q :=
    \cancelx
    \consuming p |-> alloc.tokenR (σ:=σ) ty q
    \proving{(storage_p : ptr) overhead} p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \deduce{(storage_p' : ptr) (overhead' : N) sz} [| size_of _ ty = Some sz |]
    \deduce storage_p' .[ Tbyte ! -overhead' ] |-> allocatedR q (overhead' + sz)
    \through [| storage_p = storage_p' |]
    \through [| overhead = overhead' |]%N
    \end.
  Next Obligation.
    rewrite alloc.tokenR.unlock. work.
    iExists storage_p.
    work.
    iExists overhead. work.
  Qed.

  #[global] Instance alloc_token_new_token_learnable ty q q' a b c :
    Learnable (alloc.tokenR ty q) (new_token.R q' (new_token.mk a b c)) [ty = a].
  Proof. solve_learnable. Qed.
  #[global] Instance allocatedR_learn : Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) allocatedR).
  Proof. solve_learnable. Qed.

  #[global] Instance token_learn : Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) alloc.tokenR).
  Proof. solve_learnable. Qed.

  (** <<delete nullptr>> hints
      The needs for hints at that AST level is sub-optimal, but something that requires
      a bit more infrastructure to automate. Specifically, [wp_delete_null] reduces to
      a conjunction which requires splitting the proof. However, this split can be
      avoided if <<operator delete(nullptr, ...)>> is effectively a no-op (as its
      specification says that it should be). A better phrasing of this might be a class
      like [TrivialOnNull function_name] which would allow us to generalize these proofs.
   *)
  #[program]
  Definition wp_delete_null_operator_delete_size_C module cls Q
    (Hdelete : delete_operator.delete_for module "operator delete(void*, unsigned long)" cls =[Vm]=> Some ("operator delete(void*, unsigned long)"%cpp_name, delete_operator.mk None true false))
    {sz} (Hsizeof : sizeof._size_of module cls =[Vm]=> Some sz)
    :=
    \cancelx
    \using operator_delete_size
    \using denoteModule module
    \proving wp_delete_null "operator delete(void*, unsigned long)" cls Q
    \through Q
    \end.
  Next Obligation.
    intros * Hdel * Hsize.
    rewrite wp_delete_null.unlock.
    iIntros "[#? #M] ?".
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    inversion Hdel.
    erewrite delete_operator.delete_for_submodule;
      [ | eassumption
      | apply genv_compat_submodule; eauto ].
    work. inversion Hsize as [Hx]; clear Hsize.
    rewrite wp_invoke_delete.unlock; simpl.
    work.
    rewrite /delete_operator.type_for/=.
    iApply invoke.use_cptrR; eauto; eauto.
    simpl.
    go.
  Qed.

  #[program]
  Definition wp_delete_null_operator_delete_C module cls Q
    (Hdelete : delete_operator.delete_for module "operator delete(void* )" cls =[Vm]=> Some ("operator delete(void* )"%cpp_name, delete_operator.mk None false false))
    {sz} (Hsizeof : sizeof._size_of module cls =[Vm]=> Some sz)
    :=
    \cancelx
    \using operator_delete
    \using denoteModule module
    \proving wp_delete_null "operator delete(void* )" cls Q
    \through Q
    \end.
  Next Obligation.
    intros * Hdel * Hsize.
    rewrite wp_delete_null.unlock.
    iIntros "[#? #M] ?".
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    inversion Hdel.
    erewrite delete_operator.delete_for_submodule;
      [ | eassumption
      | apply genv_compat_submodule; eauto ].
    work. inversion Hsize as [Hx]; clear Hsize.
    rewrite wp_invoke_delete.unlock; simpl.
    work.
    rewrite /delete_operator.type_for/=.
    iApply invoke.use_cptrR; eauto; eauto.
    simpl.
    go.
  Qed.

  #[program]
  Definition wp_delete_null_operator_delete_array_size_C module cls Q
    (Hdelete : delete_operator.delete_for module "operator delete[](void*, unsigned long)" (Tincomplete_array cls) =[Vm]=> Some ("operator delete[](void*, unsigned long)"%cpp_name, delete_operator.mk None true false))
    {sz} (Hsizeof : sizeof._size_of module cls =[Vm]=> Some sz)
    :=
    \cancelx
    \using operator_delete_array_size
    \using denoteModule module
    \proving wp_delete_null "operator delete[](void*, unsigned long)" (Tincomplete_array cls) Q
    \through Q
    \end.
  Next Obligation.
    intros * Hdel * Hsize.
    rewrite wp_delete_null.unlock.
    iIntros "[#? #M] ?".
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    inversion Hdel.
    erewrite delete_operator.delete_for_submodule;
      [ | eassumption
      | apply genv_compat_submodule; eauto ].
    work. inversion Hsize as [Hx]; clear Hsize.
    rewrite wp_invoke_delete.unlock; simpl.
    work.
    iApply invoke.use_cptrR; eauto; eauto.
    simpl. go.
  Qed.

  #[program]
  Definition wp_delete_null_operator_delete_array_C module cls Q
    (Hdelete : delete_operator.delete_for module "operator delete[](void* )" (Tincomplete_array cls) =[Vm]=> Some ("operator delete[](void* )"%cpp_name, delete_operator.mk None false false))
    {sz} (Hsizeof : sizeof._size_of module cls =[Vm]=> Some sz)
    :=
    \cancelx
    \using operator_delete_array
    \using denoteModule module
    \proving wp_delete_null "operator delete[](void* )" (Tincomplete_array cls) Q
    \through Q
    \end.
  Next Obligation.
    intros * Hdel * Hsize.
    rewrite wp_delete_null.unlock.
    iIntros "[#? #M] ?".
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    inversion Hdel.
    erewrite delete_operator.delete_for_submodule;
      [ | eassumption
      | apply genv_compat_submodule; eauto ].
    work. inversion Hsize as [Hx]; clear Hsize.
    rewrite wp_invoke_delete.unlock; simpl.
    work.
    iApply invoke.use_cptrR; eauto; eauto.
    go.
  Qed.

  #[program]
  Definition wp_delete_null_operator_delete_fixed_array_C module cls array_size Q
    (Hdelete : delete_operator.delete_for module "operator delete[](void*, unsigned long)" (Tarray cls array_size) =[Vm]=> Some ("operator delete[](void*, unsigned long)"%cpp_name, delete_operator.mk None true false))
    {sz} (Hsizeof : sizeof._size_of module cls =[Vm]=> Some sz)
    :=
    \cancelx
    \using operator_delete_array_size
    \using denoteModule module
    \proving wp_delete_null "operator delete[](void*, unsigned long)" (Tarray cls array_size) Q
    \through Q
    \end.
  Next Obligation.
    intros * Hdel * Hsize.
    rewrite wp_delete_null.unlock.
    iIntros "[#? #M] ?".
    iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
    inversion Hdel.
    erewrite delete_operator.delete_for_submodule;
      [ | eassumption
      | apply genv_compat_submodule; eauto ].
    work. inversion Hsize as [Hx]; clear Hsize.
    rewrite wp_invoke_delete.unlock; simpl.
    work.
    iApply invoke.use_cptrR; eauto; eauto.
    go.
  Qed.

End with_cpp.

#[global] Hint Resolve wp_delete_null_operator_delete_size_C wp_delete_null_operator_delete_C : db_bluerock_wp.
#[global] Hint Resolve wp_delete_null_operator_delete_array_C wp_delete_null_operator_delete_array_size_C
 wp_delete_null_operator_delete_fixed_array_C : db_bluerock_wp.

#[global] Hint Resolve token_prove_C token_prove_0_C | 100 : br_opacity.
#[global] Hint Resolve token_prove_using_C token_prove_using_0_C | 99 : br_opacity.
#[global] Hint Resolve token_use_non_array_C | 99 : br_opacity.
#[global] Hint Resolve token_use_array_C | 100 : br_opacity.
