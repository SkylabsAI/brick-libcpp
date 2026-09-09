Require Import iris.algebra.agree.
Require Import iris.algebra.frac.
Require Import iris.algebra.functions.
Require Import iris.algebra.gmap.
Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.
Require Import iris.algebra.lib.gmap_view.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Import linearity.

(**  Ghost state and laws for mutex specs and proofs. *)

(** MUTEX_SETS has 2 parts: `mutex_set_map g (T:get thread_idT)` for registering
  new threads and allocating their `my_mutexes g th` with
  `mutex_sets_alloc_thread`, which is a pair of  `mutex_set_auth` and
  `mutex_set_frag` of gnames.
  The thread keeps auth and trades a fraction `mutex_set_frag {[ginv]}` to
  `inv ginv P` for resources so it only gets resources once from the invariant
  until it gives resources back  (`mutex_set_frag_exclusive`).
  If `ginv` is not allcated yet, it can be allocated with
  `my_mutexes_alloc_mutex_name`.
*)
Module Type MUTEX_SETS.
  Parameter cmraR : cmra.

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Parameter mutex_set_map : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> gset thread_idT -> mpred.
  Parameter mutex_set_frag : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> thread_idT -> gset_disj iprop.gname -> mpred.
  Parameter mutex_set_auth : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> thread_idT -> gset_disj iprop.gname -> mpred.

  (** [sa] records mutexes seen by this thread; [sf] contains its available
      mutex fragments, which move to lock invariants while locks are held. *)
  Definition my_mutexes `{Σ : cpp_logic, !G Σ} γ th sa sf : mpred :=
    mutex_set_auth γ th sa ** mutex_set_frag γ th sf.

  #[global] Declare Instance mutex_set_map_timeless
      `{Σ : cpp_logic, !G Σ} γ M : Timeless (mutex_set_map γ M).
  #[global] Declare Instance mutex_set_frag_timeless
      `{Σ : cpp_logic, !G Σ} γ th s : Timeless (mutex_set_frag γ th s).
  #[global] Declare Instance mutex_set_auth_timeless
      `{Σ : cpp_logic, !G Σ} γ th s : Timeless (mutex_set_auth γ th s).
  #[global] Declare Instance my_mutexes_timeless
      `{Σ : cpp_logic, !G Σ} γ th sa sf : Timeless (my_mutexes γ th sa sf).

  #[global] Declare Instance mutex_set_map_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ M : WeaklyObjective (mutex_set_map γ M).
  #[global] Declare Instance mutex_set_frag_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ th s : WeaklyObjective (mutex_set_frag γ th s).
  #[global] Declare Instance mutex_set_auth_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ th s : WeaklyObjective (mutex_set_auth γ th s).
  #[global] Declare Instance my_mutexes_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ th sa sf : WeaklyObjective (my_mutexes γ th sa sf).

  Parameter mutex_set_frag_exclusive : forall `{Σ : cpp_logic, !G Σ} γ th γm,
    mutex_set_frag γ th (GSet {[γm]}) ** mutex_set_frag γ th (GSet {[γm]}) |-- False.
  Parameter alloc_mutex_set_map : forall `{Σ : cpp_logic, !G Σ},
    ⊢ |==> ∃ γ, mutex_set_map γ ∅.
  Parameter mutex_sets_alloc_thread : forall `{Σ : cpp_logic, !G Σ} γ T th,
    th ∉ T ->
    mutex_set_map γ T |--
      (|==> mutex_set_map γ (T ∪ {[th]}) **
              my_mutexes γ th (GSet ∅) (GSet ∅)).
  Parameter my_mutexes_alloc_mutex_name : forall `{Σ : cpp_logic, !G Σ} γ th sa sf γm,
    γm ∉ sa ->
    my_mutexes γ th (GSet sa) sf |--
      (|==> my_mutexes γ th (GSet (sa ∪ {[γm]})) sf **
              mutex_set_frag γ th (GSet {[γm]})).

  (** This is more of a sanity check. Maybe there are better rules that should 
      be included in the module instead of this.
      Distinct threads can allocate, possibly overlapping gname sets.
      Frags are given to the lock invariants while auth are held by threads. *)
  Parameter mutex_set_frags_alloc : forall `{Σ : cpp_logic, !G Σ}
      (th1 th2 : thread_idT) (s1 s2 : gset iprop.gname),
    th1 ≠ th2 ->
    ⊢ |==> ∃ γ,
      mutex_set_frag γ th1 (GSet s1) **
      mutex_set_frag γ th2 (GSet s2) **
      (mutex_set_map γ {[th1; th2]} **
       mutex_set_auth γ th1 (GSet s1) **
       mutex_set_auth γ th2 (GSet s2)).
End MUTEX_SETS.

Module Type MUTEX_TOKENS.
  Parameter cmraR : cmra.

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> Qp -> mpred.
  Parameter given_token : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> Qp -> mpred.

  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  #[global] Declare Instance given_token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (given_token γ).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  #[global] Declare Instance given_token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (given_token γ q).

  Parameter token_full token_not_full : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> mpred.
  #[global] Declare Instance token_full_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ : WeaklyObjective (token_full γ).
  #[global] Declare Instance token_not_full_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ : WeaklyObjective (token_not_full γ).

  Parameter token_full_init : forall `{Σ : cpp_logic, !G Σ} γ,
    given_token γ 1 |-- token_full γ.
  Parameter acquire : forall `{Σ : cpp_logic, !G Σ} γ q,
    token_full γ ** token γ q |-- given_token γ q ** token_not_full γ.
  Parameter release : forall `{Σ : cpp_logic, !G Σ} γ q,
    token_not_full γ ** given_token γ q |-- token γ q ** token_full γ.
  Parameter token_not_full_full_token : forall `{Σ : cpp_logic, !G Σ} γ,
    token_not_full γ ** token γ 1 |-- False.

  Parameter alloc : forall `{Σ : cpp_logic, !G Σ},
    ⊢ |==> ∃ γ, token γ 1 ** given_token γ 1.
End MUTEX_TOKENS.

(** Authoritative and exclusive fragment ownership of an optional thread ID. *)
Module Type OWNER_TID.
  Parameter cmraR : cmra.

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Parameter owner_tid_auth owner_tid_frag : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> option thread_idT -> mpred.

  #[global] Declare Instance owner_tid_auth_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_auth γ o).
  #[global] Declare Instance owner_tid_frag_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_frag γ o).
  #[global] Declare Instance owner_tid_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_tid_frag γ).
  #[global] Declare Instance owner_tid_auth_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_auth γ o).
  #[global] Declare Instance owner_tid_frag_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_frag γ o).
  #[global] Declare Instance owner_agree
      `{Σ : cpp_logic, !G Σ} γ o1 o2 :
    Observe2 [| o1 = o2 |] (owner_tid_auth γ o1) (owner_tid_frag γ o2).

  Parameter alloc : forall `{Σ : cpp_logic, !G Σ} o,
    ⊢ |==> ∃ γ, owner_tid_auth γ o ** owner_tid_frag γ o.
  Parameter owner_update : forall `{Σ : cpp_logic, !G Σ} γ oa ofrag o',
    owner_tid_auth γ oa ** owner_tid_frag γ ofrag |--
      (|==> owner_tid_auth γ o' ** owner_tid_frag γ o').
End OWNER_TID.

(** A MUTEX_STATE says a mutex spec is parametrized by some `token`, `not_locked`
  and `locked`. The exact model depends on the implementation. *)
Module Type MUTEX_STATE.
  Parameter gname : Set.
  Parameter Q : Type.
  (* FIXME do we need these? *)
  Parameter pool_name inv_name : gname -> iprop.gname.

  Parameter G : forall `{Σ : cpp_logic}, Type.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.

  (** [Q] describes the permissions transferred by lock and unlock. *)
  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    gname -> Qp -> mpred.
  Parameter not_locked locked : forall `{Σ : cpp_logic, !G Σ} {σ : genv},
    ptr -> gname -> thread_idT -> Q -> mpred.

  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  #[global] Declare Instance locked_timeless
      `{Σ : cpp_logic, !G Σ} {σ : genv} this γ th q :
    Timeless (locked this γ th q).
  #[global] Declare Instance locked_exclusive
      `{Σ : cpp_logic, !G Σ} {σ : genv} this γ q :
    Exclusive1 (fun th => locked this γ th q).
End MUTEX_STATE.

(* Proofs that the ghost state modules are inhabited. *)

Module MutexSets : MUTEX_SETS.
  Canonical Structure threadR := authUR (gset_disjR iprop.gname).
  Canonical Structure cmraR : cmra :=
    discrete_funUR (fun _ : thread_idT => threadR).

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.


  Definition mutex_set_auth `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (th : thread_idT) (s : gset_disj iprop.gname) : mpred :=
    own γ (discrete_fun_singleton th (● s) : cmraR).

  Definition mutex_set_frag `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (th : thread_idT) (s : gset_disj iprop.gname) : mpred :=
    own γ (discrete_fun_singleton th (◯ s) : cmraR).

  Definition my_mutexes `{Σ : cpp_logic, !G Σ} γ th sa sf : mpred :=
    mutex_set_auth γ th sa ** mutex_set_frag γ th sf.

  Definition reserve (M : gset thread_idT) : cmraR :=
    fun th => if decide (th ∈ M) then ε else ● (GSet ∅).

  Definition mutex_set_map `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (M : gset thread_idT) : mpred :=
    own γ (reserve M).

  #[global] Instance mutex_set_map_timeless `{Σ : cpp_logic, !G Σ} γ M :
    Timeless (mutex_set_map γ M).
  Proof. rewrite /mutex_set_map. apply _. Qed.
  #[global] Instance mutex_set_frag_timeless `{Σ : cpp_logic, !G Σ} γ th s :
    Timeless (mutex_set_frag γ th s).
  Proof. rewrite /mutex_set_frag. apply _. Qed.
  #[global] Instance mutex_set_auth_timeless `{Σ : cpp_logic, !G Σ} γ th s :
    Timeless (mutex_set_auth γ th s).
  Proof. rewrite /mutex_set_auth. apply _. Qed.
  #[global] Instance my_mutexes_timeless `{Σ : cpp_logic, !G Σ} γ th sa sf :
    Timeless (my_mutexes γ th sa sf).
  Proof. rewrite /my_mutexes. apply _. Qed.

  #[global] Instance mutex_set_map_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ M :
    WeaklyObjective (mutex_set_map γ M).
  Proof. rewrite /mutex_set_map. apply _. Qed.
  #[global] Instance mutex_set_frag_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ th s :
    WeaklyObjective (mutex_set_frag γ th s).
  Proof. rewrite /mutex_set_frag. apply _. Qed.
  #[global] Instance mutex_set_auth_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ th s :
    WeaklyObjective (mutex_set_auth γ th s).
  Proof. rewrite /mutex_set_auth. apply _. Qed.
  #[global] Instance my_mutexes_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ th sa sf :
    WeaklyObjective (my_mutexes γ th sa sf).
  Proof. rewrite /my_mutexes. apply _. Qed.

  Section theory.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma mutex_set_frag_exclusive γ th γm :
      mutex_set_frag γ th (GSet {[γm]}) **
      mutex_set_frag γ th (GSet {[γm]}) |-- False.
    Proof.
      rewrite /mutex_set_frag.
      iIntros "[H1 H2]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
      iPureIntro.
      specialize (Hvalid th).
      rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton in Hvalid.
      rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in Hvalid.
      set_solver.
    Qed.

    Lemma alloc_mutex_set_map :
      ⊢ |==> ∃ γ, mutex_set_map γ ∅.
    Proof.
      iMod (own_alloc (reserve ∅)) as (γ) "Hmap".
      { intros th. rewrite /reserve.
        apply auth_auth_valid. done. }
      iModIntro. iExists γ. iExact "Hmap".
    Qed.

    Lemma my_mutexes_alloc_mutex_name γ th sa sf γm :
      γm ∉ sa ->
      my_mutexes γ th (GSet sa) sf |--
        (|==> my_mutexes γ th (GSet (sa ∪ {[γm]})) sf **
                mutex_set_frag γ th (GSet {[γm]})).
    Proof.
      rewrite /my_mutexes /mutex_set_auth /mutex_set_frag.
      iIntros (Hfresh) "[HA HF]".
      iMod (own_update γ _
        ((discrete_fun_singleton th (● GSet (sa ∪ {[γm]})) ⋅
          discrete_fun_singleton th (◯ GSet {[γm]})) : cmraR)
        with "HA") as "[HA Hnew]".
      { rewrite discrete_fun_singleton_op.
        apply discrete_fun_singleton_update.
        rewrite (comm_L union).
        apply auth_update_alloc.
        apply gset_disj_alloc_empty_local_update. set_solver. }
      iModIntro. iFrame.
    Qed.

    Lemma mutex_sets_alloc_thread_with_set
        γ (T : gset thread_idT) th (s : gset iprop.gname) :
      th ∉ T ->
      mutex_set_map γ T |--
        (|==> mutex_set_map γ (T ∪ {[th]}) **
              my_mutexes γ th (GSet s) (GSet s)).
    Proof.
      rewrite /mutex_set_map /my_mutexes /mutex_set_auth /mutex_set_frag.
      iIntros (Hfresh) "Hmap".
      iMod (own_update γ _ (reserve (T ∪ {[th]}) ⋅
        (discrete_fun_singleton th (● GSet s) ⋅ discrete_fun_singleton th (◯ GSet s)))
        with "Hmap") as "[Hmap [HA HF]]".
      { apply discrete_fun_update. intros th'.
        rewrite !discrete_fun_lookup_op.
        destruct (decide (th = th')) as [<-|Hne].
        - rewrite !discrete_fun_lookup_singleton /reserve.
          case_decide; first contradiction.
          case_decide; last set_solver.
          rewrite left_id.
          apply auth_update_alloc.
          rewrite -{1}(right_id_L ∅ union s).
          apply gset_disj_alloc_empty_local_update. set_solver.
        - rewrite !discrete_fun_lookup_singleton_ne; try done.
          rewrite left_id right_id /reserve.
          destruct (decide (th' ∈ T)).
          + rewrite !decide_True; try set_solver.
          + rewrite !decide_False; try set_solver.
      }
      iModIntro. iFrame.
    Qed.

    Lemma mutex_sets_alloc_thread γ T th :
      th ∉ T ->
      mutex_set_map γ T |--
        (|==> mutex_set_map γ (T ∪ {[th]}) **
                my_mutexes γ th (GSet ∅) (GSet ∅)).
    Proof. apply mutex_sets_alloc_thread_with_set. Qed.

    Lemma mutex_set_frags_alloc (th1 th2 : thread_idT) (s1 s2 : gset iprop.gname) :
      th1 ≠ th2 ->
      ⊢ |==> ∃ γ,
        mutex_set_frag γ th1 (GSet s1) **
        mutex_set_frag γ th2 (GSet s2) **
        (mutex_set_map γ {[th1; th2]} **
         mutex_set_auth γ th1 (GSet s1) **
         mutex_set_auth γ th2 (GSet s2)).
    Proof.
      iIntros (Hneq).
      iMod alloc_mutex_set_map as (γ) "Hmap".
      iMod (mutex_sets_alloc_thread_with_set γ ∅ th1 s1 ltac:(set_solver)
        with "Hmap") as "[Hmap Ht1]".
      iEval (rewrite left_id_L) in "Hmap".
      iMod (mutex_sets_alloc_thread_with_set γ {[th1]} th2 s2 ltac:(set_solver)
        with "Hmap") as "[Hmap Ht2]".
      iDestruct "Ht1" as "[Ha1 Hf1]".
      iDestruct "Ht2" as "[Ha2 Hf2]".
      iModIntro. iExists γ. iFrame.
    Qed.

  End theory.

  #[global] Hint Opaque mutex_set_map mutex_set_auth mutex_set_frag
    my_mutexes : sl_opacity typeclass_instances.
End MutexSets.

(** ** The fractional token/given-token pair *)

Module MutexTokens <: MUTEX_TOKENS.
  Canonical Structure cmraR : cmra :=
    prodUR (optionUR fracR) (optionUR fracR).

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition token `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (q : Qp) : mpred :=
    own γ (Some q, None).

  Definition given_token `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (q : Qp) : mpred :=
    own γ (None, Some q).

  #[global] Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  Proof.
    intros q1 q2. rewrite /token -own_op /=. done.
  Qed.

  #[global] Instance given_token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (given_token γ).
  Proof.
    intros q1 q2. rewrite /given_token -own_op /=. done.
  Qed.

  #[global] Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  Proof. rewrite /token. apply _. Qed.

  #[global] Instance given_token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (given_token γ q).
  Proof. rewrite /given_token. apply _. Qed.

  (** Ordinary and given-token shares in the invariant add up to one.
      [token_not_full] contains a positive ordinary-token share, so it conflicts
      with the full ordinary token required for destruction. *)
  Definition token_not_full `{Σ : cpp_logic, !G Σ} (γ : iprop.gname) : mpred :=
    token γ 1 ∨ ∃ qt qg : Qp,
      [| (qt + qg = 1)%Qp |] ** token γ qt ** given_token γ qg.

  (** Include the endpoint with no ordinary tokens. Transfers preserve the
      balance even when a caller returns only part of its given-token share. *)
  Definition token_full `{Σ : cpp_logic, !G Σ} (γ : iprop.gname) : mpred :=
    given_token γ 1 ∨ token_not_full γ.

  #[global] Instance token_full_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ :
    WeaklyObjective (token_full γ).
  Proof. rewrite /token_full /token_not_full /token /given_token. apply _. Qed.

  #[global] Instance token_not_full_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ :
    WeaklyObjective (token_not_full γ).
  Proof. rewrite /token_not_full /token /given_token. apply _. Qed.

  #[global] Hint Opaque token given_token token_not_full token_full : sl_opacity typeclass_instances.

  Section theory.
    Context `{Σ : cpp_logic, !G Σ}.

    #[local] Existing Instance mpred_BiAffine.

    Lemma token_full_init γ : given_token γ 1 |-- token_full γ.
    Proof. rewrite /token_full. iIntros "T". iLeft. iExact "T". Qed.

    Lemma token_valid γ q : token γ q |-- [| (q ≤ 1)%Qp |].
    Proof.
      rewrite /token. iIntros "H".
      iDestruct (own_valid with "H") as %Hvalid.
      iPureIntro. exact (proj1 Hvalid).
    Qed.

    Lemma given_token_valid γ q : given_token γ q |-- [| (q ≤ 1)%Qp |].
    Proof.
      rewrite /given_token. iIntros "H".
      iDestruct (own_valid with "H") as %Hvalid.
      iPureIntro. exact (proj2 Hvalid).
    Qed.

    Lemma token_valid_2 γ q1 q2 :
      token γ q1 ** token γ q2 |-- [| (q1 + q2 ≤ 1)%Qp |].
    Proof. rewrite -fractional. apply token_valid. Qed.

    Lemma given_token_valid_2 γ q1 q2 :
      given_token γ q1 ** given_token γ q2 |-- [| (q1 + q2 ≤ 1)%Qp |].
    Proof. rewrite -fractional. apply given_token_valid. Qed.

    Lemma token_not_full_full_token γ :
      token_not_full γ ** token γ 1 |-- False.
    Proof.
      rewrite /token_not_full. iIntros "[H T]".
      iDestruct "H" as "[H | H]".
      - iDestruct (token_valid_2 with "[$T $H]") as %Hbad.
        exfalso. exact (Qp.not_add_le_l 1 1 Hbad).
      - iDestruct "H" as (qt qg) "(_ & H & _)".
        iDestruct (token_valid_2 with "[$T $H]") as %Hbad.
        exfalso. exact (Qp.not_add_le_l 1 qt Hbad).
    Qed.

    Lemma acquire γ q :
      token_full γ ** token γ q |-- given_token γ q ** token_not_full γ.
    Proof.
      rewrite /token_full /token_not_full. iIntros "[H T]".
      iDestruct "H" as "[H | [H | H]]".
      - iDestruct (token_valid with "T") as %Hq.
        apply Qp.le_lteq in Hq as [Hq | ->].
        + apply Qp.lt_sum in Hq as [r Hr].
          iEval (rewrite Hr fractional) in "H".
          iDestruct "H" as "[H R]". iFrame "H".
          iRight. iExists q, r. iFrame. done.
        + iFrame "H". iLeft. iExact "T".
      - iDestruct (token_valid_2 with "[$H $T]") as %Hbad.
        exfalso. exact (Qp.not_add_le_l 1 q Hbad).
      - iDestruct "H" as (qt qg) "(%Hsum & T0 & G)".
        iDestruct (token_valid_2 with "[$T0 $T]") as %Hvalid.
        rewrite -Hsum in Hvalid.
        apply Qp.add_le_mono_l, Qp.le_lteq in Hvalid as [Hlt | ->].
        + apply Qp.lt_sum in Hlt as [r Hr].
          iEval (rewrite Hr fractional) in "G".
          iDestruct "G" as "[G R]". iFrame "G".
          iRight. iExists (qt + q)%Qp, r.
          iSplit; first (iPureIntro; by rewrite -Qp.add_assoc -Hr).
          iFrame "R". rewrite fractional. iFrame.
        + iFrame "G". iLeft. rewrite -Hsum fractional. iFrame.
    Qed.

    Lemma release γ q :
      token_not_full γ ** given_token γ q |-- token γ q ** token_full γ.
    Proof.
      rewrite /token_full /token_not_full. iIntros "[H G]".
      iDestruct "H" as "[H | H]".
      - iDestruct (given_token_valid with "G") as %Hq.
        apply Qp.le_lteq in Hq as [Hq | ->].
        + apply Qp.lt_sum in Hq as [r Hr].
          iEval (rewrite Hr fractional) in "H".
          iDestruct "H" as "[H R]". iFrame "H".
          iRight. iRight. iExists r, q. iFrame.
          iPureIntro. by rewrite Qp.add_comm.
        + iFrame "H". iLeft. iExact "G".
      - iDestruct "H" as (qt qg) "(%Hsum & T & G0)".
        iDestruct (given_token_valid_2 with "[$G $G0]") as %Hvalid.
        rewrite -Hsum in Hvalid.
        apply Qp.add_le_mono_r, Qp.le_lteq in Hvalid as [Hlt | ->].
        + apply Qp.lt_sum in Hlt as [r Hr].
          iEval (rewrite Hr fractional) in "T".
          iDestruct "T" as "[T R]". iFrame "T".
          iRight. iRight. iExists r, (q + qg)%Qp.
          iSplit; first (iPureIntro; by rewrite Qp.add_assoc (Qp.add_comm r q) -Hr).
          iFrame "R". rewrite fractional. iFrame.
        + iFrame "T". iLeft. rewrite -Hsum fractional. iFrame.
    Qed.

    Lemma alloc :
      ⊢ |==> ∃ γ, token γ 1 ** given_token γ 1.
    Proof.
      iMod (own_alloc
        (((Some 1%Qp, None) ⋅ (None, Some 1%Qp)) : cmraR)) as (γ) "H".
      { done. }
      iModIntro. iExists γ.
      rewrite /token /given_token -own_op. iExact "H".
    Qed.
  End theory.
End MutexTokens.

(** The exclusive-authoritative implementation of [OWNER_TID]. *)
Module OwnerTid : OWNER_TID.
  Canonical Structure cmraR : cmra := excl_authR (optionO thread_idTO).

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition owner_tid_auth `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (o : option thread_idT) : mpred :=
    own γ ((●E o) : cmraR).
  Definition owner_tid_frag `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (o : option thread_idT) : mpred :=
    own γ ((◯E o) : cmraR).

  #[global] Instance owner_tid_auth_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_auth γ o).
  Proof. rewrite /owner_tid_auth. apply _. Qed.
  #[global] Instance owner_tid_frag_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_frag γ o).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_tid_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_tid_frag γ).
  Proof.
    intros o1 o2. rewrite /owner_tid_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid. rewrite excl_auth_frag_op_valid. done.
  Qed.

  #[global] Instance owner_tid_auth_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_auth γ o).
  Proof. rewrite /owner_tid_auth. apply _. Qed.
  #[global] Instance owner_tid_frag_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_frag γ o).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_agree `{Σ : cpp_logic, !G Σ} γ o1 o2 :
    Observe2 [| o1 = o2 |] (owner_tid_auth γ o1) (owner_tid_frag γ o2).
  Proof.
    apply observe_2_intro_only_provable.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "A F".
    iDestruct (own_valid_2 with "A F") as %HV.
    iPureIntro. apply leibniz_equiv, excl_auth_agree, HV.
  Qed.

  Lemma alloc `{Σ : cpp_logic, !G Σ} o :
    ⊢ |==> ∃ γ, owner_tid_auth γ o ** owner_tid_frag γ o.
  Proof.
    iMod (own_alloc ((●E o ⋅ ◯E o) : cmraR)) as (γ) "H".
    { apply excl_auth_valid. }
    iModIntro. iExists γ.
    rewrite /owner_tid_auth /owner_tid_frag -own_op. iExact "H".
  Qed.

  Lemma owner_update `{Σ : cpp_logic, !G Σ} γ oa ofrag o' :
    owner_tid_auth γ oa ** owner_tid_frag γ ofrag |--
      (|==> owner_tid_auth γ o' ** owner_tid_frag γ o').
  Proof.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "[A F]".
    iMod (own_update_2 with "A F") as "[$ $]";
      first apply (excl_auth_update _ _ o').
    done.
  Qed.

  #[global] Hint Opaque owner_tid_auth owner_tid_frag : sl_opacity typeclass_instances.
End OwnerTid.
