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

Module Type MUTEX_SETS.
  Parameter cmraR : cmra.

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  (** All predicates use the same ghost name [γ], with [th] selecting an
      entry. [mutex_set_map γ T] retains the authorities for thread IDs
      outside the allocated set [T]. *)
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

  (** Distinct threads can own arbitrary, possibly overlapping mutex sets.
      The registry and both authoritative sets are retained as the remainder. *)
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

Module Type MUTEX_STATE.
  Parameter gname : Set.
  Parameter (pool_name : gname -> iprop.gname).

  Parameter G : forall `{Σ : cpp_logic}, Type.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.

  (** Client resources. [not_locked] permits this thread to attempt acquisition;
      [locked] records ownership after successful acquisition. *)
  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    gname -> Qp -> mpred.
  Parameter not_locked : forall `{Σ : cpp_logic, !G Σ},
    gname -> thread_idT -> Qp -> iprop.gname -> mpred.
  Parameter locked : forall `{Σ : cpp_logic, !G Σ},
    gname -> option thread_idT -> Qp -> mpred.

  (** The ghost resources kept inside the mutex invariant. The boolean agrees
      with the physical lock bit; the invariant name connects acquisitions to
      the same mutex. Its representation is private to the implementation. *)
  Parameter state : forall `{Σ : cpp_logic, !G Σ},
    gname -> iprop.gname -> bool -> mpred.
  #[global] Declare Instance state_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ inv_gname b :
    WeaklyObjective (state γ inv_gname b).

  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  #[global] Declare Instance locked_timeless
      `{Σ : cpp_logic, !G Σ} γ th q : Timeless (locked γ th q).
  #[global] Declare Instance locked_exclusive
      `{Σ : cpp_logic, !G Σ} γ q : Exclusive1 (fun th => locked γ th q).

  (** Each mutex uses the caller's shared mutex-set pool. *)
  Parameter alloc : forall `{Σ : cpp_logic, !G Σ} (γpool : iprop.gname) inv_gname,
    ⊢ |==> ∃ γ, [| pool_name γ = γpool |] **
      token γ 1 ** state γ inv_gname false.

  (** Successful acquisition and release exchange client resources with the
      invariant. Failed acquisition leaves both resources unchanged. *)
  Parameter do_lock : forall `{Σ : cpp_logic, !G Σ} γ inv_gname th q,
    state γ inv_gname false ** not_locked γ th q inv_gname |--
      (|==> state γ inv_gname true ** locked γ (Some th) q).
  Parameter do_unlock : forall `{Σ : cpp_logic, !G Σ} γ inv_gname th q,
    state γ inv_gname true ** locked γ (Some th) q |--
      (|==> state γ inv_gname false ** not_locked γ th q inv_gname).

  (** Ownership rules out an unlocked physical state. Full destruction
      permission rules out a locked physical state. *)
  Parameter unlocked_locked : forall `{Σ : cpp_logic, !G Σ} γ inv_gname th q,
    state γ inv_gname false ** locked γ th q |-- False.
  Parameter locked_full_token : forall `{Σ : cpp_logic, !G Σ} γ inv_gname,
    state γ inv_gname true ** token γ 1 |-- False.
End MUTEX_STATE.

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

Module MutexTokens.
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

(** The concrete state abstracts over mutex sets and tokens, and implements
    optional owner state directly. *)
Module MakeMutexState
    (Sets0 : MUTEX_SETS)
    (Tokens0 : MUTEX_TOKENS) <: MUTEX_STATE.
  Module Sets := Sets0.
  Module Tokens := Tokens0.

  #[local] Existing Instance Tokens.token_fractional.
  #[local] Existing Instance Tokens.given_token_fractional.
  #[local] Existing Instance Tokens.token_timeless.
  #[local] Existing Instance Tokens.given_token_timeless.

  Canonical Structure owner_cmraR : cmra :=
    excl_authR (optionO thread_idTO).

  Record mutex_gname : Set := MkGname {
    pool_gname : iprop.gname;
    token_gname : iprop.gname;
    owner_gname : iprop.gname;
  }.
  Definition gname : Set := mutex_gname.
  Definition pool_name (γ : gname) : iprop.gname := γ.(pool_gname).

  Class stateG `{Σ : cpp_logic} := {
    #[global] sets_G :: Sets.G Σ;
    #[global] tokens_G :: Tokens.G Σ;
    #[global] has_owner :: HasOwn (iPropI _Σ) owner_cmraR;
    #[global] has_owner_upd :: HasOwnUpd (iPropI _Σ) owner_cmraR;
    #[global] has_owner_valid :: HasOwnValid (iPropI _Σ) owner_cmraR;
  }.
  Definition G := @stateG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance state_G `{Σ : cpp_logic} (H : G Σ) : @stateG _ _ Σ := H.

  Definition owner_tid_auth `{Σ : cpp_logic, !G Σ}
      (γ : gname) (o_thr : option thread_idT) : mpred :=
    own γ.(owner_gname) ((●E o_thr) : owner_cmraR).

  Definition owner_tid_frag `{Σ : cpp_logic, !G Σ}
      (γ : gname) (o_thr : option thread_idT) : mpred :=
    own γ.(owner_gname) ((◯E o_thr) : owner_cmraR).

  #[global] Hint Opaque owner_tid_auth owner_tid_frag : sl_opacity typeclass_instances.

  #[only(timeless)] derive owner_tid_auth.
  #[only(timeless)] derive owner_tid_frag.

  #[global] Instance owner_tid_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_tid_frag γ).
  Proof.
    intros o_thr1 o_thr2. rewrite /owner_tid_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid. rewrite excl_auth_frag_op_valid. done.
  Qed.

  #[global] Instance owner_tid_auth_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ o_thr :
    WeaklyObjective (owner_tid_auth γ o_thr).
  Proof. rewrite /owner_tid_auth. apply _. Qed.

  #[global] Instance owner_tid_frag_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ o_thr :
    WeaklyObjective (owner_tid_frag γ o_thr).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_agree `{Σ : cpp_logic, !G Σ} γ o1 o2 :
    Observe2 [| o1 = o2 |] (owner_tid_auth γ o1) (owner_tid_frag γ o2).
  Proof.
    apply observe_2_intro_only_provable.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "A F".
    iDestruct (own_valid_2 with "A F") as %HV.
    iPureIntro. apply leibniz_equiv, excl_auth_agree, HV.
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

  Definition token `{Σ : cpp_logic, !G Σ}
      (γ : gname) (q : Qp) : mpred :=
    Tokens.token γ.(token_gname) q.

  Definition not_locked `{Σ : cpp_logic, !G Σ}
      (γ : gname) (th : thread_idT) (q : Qp)
      (inv_gname : iprop.gname) : mpred :=
    Sets.mutex_set_frag γ.(pool_gname) th (GSet {[inv_gname]}) **
    Tokens.token γ.(token_gname) q.

  Definition locked `{Σ : cpp_logic, !G Σ}
      (γ : gname) (o_thr : option thread_idT) (q : Qp) : mpred :=
    Tokens.given_token γ.(token_gname) q **
    owner_tid_frag γ o_thr.

  Lemma not_locked_eq `{Σ : cpp_logic, !G Σ} γ th q inv_gname :
    not_locked γ th q inv_gname ⊣⊢
      Sets.mutex_set_frag γ.(pool_gname) th (GSet {[inv_gname]}) **
      Tokens.token γ.(token_gname) q.
  Proof. done. Qed.

  Lemma locked_eq `{Σ : cpp_logic, !G Σ} γ o_thr q :
    locked γ o_thr q ⊣⊢
      Tokens.given_token γ.(token_gname) q **
      owner_tid_frag γ o_thr.
  Proof. done. Qed.

  #[global] Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  Proof. rewrite /token. apply Tokens.token_fractional. Qed.

  #[global] Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  Proof. rewrite /token. apply _. Qed.

  #[global] Instance locked_timeless
      `{Σ : cpp_logic, !G Σ} γ th q : Timeless (locked γ th q).
  Proof. rewrite /locked. apply _. Qed.

  #[global] Instance locked_exclusive
      `{Σ : cpp_logic, !G Σ} γ q : Exclusive1 (fun th => locked γ th q).
  Proof.
    intros th1 th2. rewrite /locked.
    apply _.
  Qed.

  (** While held, the invariant owns this thread's singleton mutex fragment
      and the token balance. The thread retains its mutex-set authority.
      When free, both halves of the previous owner remain in the invariant. *)
  Definition state `{Σ : cpp_logic, !G Σ}
      (γ : gname) (inv_gname : iprop.gname) (b : bool) : mpred :=
    (if b then
      ∃ th, owner_tid_auth γ (Some th) **
        Sets.mutex_set_frag γ.(pool_gname) th (GSet {[inv_gname]}) **
        Tokens.token_not_full γ.(token_gname)
    else
      ∃ owner, owner_tid_auth γ owner ** owner_tid_frag γ owner **
        Tokens.token_full γ.(token_gname))%I.

  #[global] Instance state_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ inv_gname b :
    WeaklyObjective (state γ inv_gname b).
  Proof. rewrite /state. destruct b; apply _. Qed.

  Section state_laws.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma alloc (γpool : iprop.gname) inv_gname :
      ⊢ |==> ∃ γ, [| pool_name γ = γpool |] **
        token γ 1 ** state γ inv_gname false.
    Proof.
      iMod Tokens.alloc as (gt) "[T GT]".
      iMod (own_alloc ((●E None ⋅ ◯E None) : owner_cmraR)) as (go) "O".
      { apply excl_auth_valid. }
      iDestruct (own_op with "O") as "[OA OF]".
      iModIntro. iExists (MkGname γpool gt go).
      iSplit; first done.
      rewrite /token /state /=. iFrame "T". iExists None.
      rewrite /owner_tid_auth /owner_tid_frag /=. iFrame "OA OF".
      iApply Tokens.token_full_init. iExact "GT".
    Qed.

    Lemma do_lock γ inv_gname th q :
      state γ inv_gname false ** not_locked γ th q inv_gname |--
        (|==> state γ inv_gname true ** locked γ (Some th) q).
    Proof.
      rewrite /state /not_locked /locked.
      iIntros "[State [Sets T]]".
      iDestruct "State" as (owner) "(OA & OF & Balance)".
      iDestruct (Tokens.acquire with "[$Balance $T]") as "[GT Balance]".
      iMod (owner_update _ _ _ (Some th) with "[$OA $OF]") as "[OA OF]".
      iModIntro. iFrame "GT OF". iExists th. iFrame.
    Qed.

    Lemma do_unlock γ inv_gname th q :
      state γ inv_gname true ** locked γ (Some th) q |--
        (|==> state γ inv_gname false ** not_locked γ th q inv_gname).
    Proof.
      rewrite /state /locked /not_locked.
      iIntros "[State [GT OF]]".
      iDestruct "State" as (owner) "(OA & Sets & Balance)".
      iDestruct (observe_2 [| Some owner = Some th |] with "OA OF") as %Heq.
      injection Heq as ->.
      iDestruct (Tokens.release with "[$Balance $GT]") as "[T Balance]".
      iModIntro. iFrame "Sets T". iExists (Some th). iFrame.
    Qed.

    Lemma unlocked_locked γ inv_gname th q :
      state γ inv_gname false ** locked γ th q |-- False.
    Proof.
      rewrite /state /locked. iIntros "[State [_ OF]]".
      iDestruct "State" as (owner) "(_ & OF0 & _)".
      iDestruct (owner_tid_frag_exclusive with "OF0 OF") as %[].
    Qed.

    Lemma locked_full_token γ inv_gname :
      state γ inv_gname true ** token γ 1 |-- False.
    Proof.
      rewrite /state /token. iIntros "[State T]".
      iDestruct "State" as (th) "(_ & _ & Balance)".
      iApply (Tokens.token_not_full_full_token with "[$Balance $T]").
    Qed.
  End state_laws.

  #[global] Hint Opaque token not_locked locked state : sl_opacity typeclass_instances.

End MakeMutexState.

Module LockState := MakeMutexState MutexSets MutexTokens.
