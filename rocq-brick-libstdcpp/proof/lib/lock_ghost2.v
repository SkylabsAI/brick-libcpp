Require Import iris.algebra.agree.
Require Import iris.algebra.frac.
Require Import iris.algebra.functions.
Require Import iris.algebra.gmap.
Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.
Require Import iris.algebra.lib.gmap_view.
Require Import iris.algebra.coPset.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Import linearity.

(**  Various ghost state constructions and laws for concurrency library specs and proofs. *)

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
  Parameter my_mutexes : forall `{Σ : cpp_logic, !G Σ},
    iprop.gname -> thread_idT -> coPset.coPset_disj -> mpred.
  
  #[global] Declare Instance mutex_set_map_timeless
      `{Σ : cpp_logic, !G Σ} γ M : Timeless (mutex_set_map γ M).
  #[global] Declare Instance my_mutexes_timeless
      `{Σ : cpp_logic, !G Σ} γ th E : Timeless (my_mutexes γ th E).

  #[global] Declare Instance mutex_set_map_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ M : WeaklyObjective (mutex_set_map γ M).
  #[global] Declare Instance my_mutexes_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ th E : WeaklyObjective (my_mutexes γ th E).

  Parameter my_mutexes_exclusive : forall `{Σ : cpp_logic, !G Σ} γ th (E1 E2: coPset),
    E1 ∩ E2 <> ∅ ->
    my_mutexes γ th (CoPset E1) **
    my_mutexes γ th (CoPset E2) |-- False.
  Parameter alloc_mutex_set_map : forall `{Σ : cpp_logic, !G Σ},
    ⊢ |==> ∃ γ, mutex_set_map γ ∅.
  Parameter mutex_sets_alloc_thread : forall `{Σ : cpp_logic, !G Σ} γ T th,
    th ∉ T ->
    mutex_set_map γ T |--
      (|==> mutex_set_map γ (T ∪ {[th]}) **
              my_mutexes γ th (CoPset ⊤)).
  Parameter my_mutexes_alloc_mutex_name : forall `{Σ : cpp_logic, !G Σ}
      γ th (E N : coPset),
    N ⊆ E ->
    my_mutexes γ th (CoPset E) |--
      my_mutexes γ th (CoPset (E \ N)) ** my_mutexes γ th (CoPset N).

  (* an example that two threads can allocate the same namespace token. *)
  Lemma my_mutexes_alloc_eg : forall `{Σ : cpp_logic, !G Σ}
      (th1 th2 : thread_idT) (N : coPset),
    th1 ≠ th2 ->
    ⊢ |==> ∃ γ,
      my_mutexes γ th1 (CoPset N) **
      my_mutexes γ th2 (CoPset N) **
      (mutex_set_map γ {[th1; th2]} **
       my_mutexes γ th1 (CoPset (⊤ \ N)) **
       my_mutexes γ th2 (CoPset (⊤ \ N))).
  Proof.
    intros until N. intros Hneq.
    iMod alloc_mutex_set_map as (γ) "Hmap".
    iMod (mutex_sets_alloc_thread γ ∅ th1 ltac:(set_solver)
      with "Hmap") as "[Hmap Ht1]".
    iEval (rewrite left_id_L) in "Hmap".
    iMod (mutex_sets_alloc_thread γ {[th1]} th2 ltac:(set_solver)
      with "Hmap") as "[Hmap Ht2]".
    iDestruct (my_mutexes_alloc_mutex_name γ th1 ⊤ N ltac:(set_solver)
      with "Ht1") as "[Hr1 Hn1]".
    iDestruct (my_mutexes_alloc_mutex_name γ th2 ⊤ N ltac:(set_solver)
      with "Ht2") as "[Hr2 Hn2]".
    iModIntro. iExists γ. iFrame.
  Qed.
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

(* Proofs that the ghost state modules are inhabited. *)

Module MutexSets : MUTEX_SETS.
  Canonical Structure cmraR : cmra :=
    discrete_funUR (fun _ : thread_idT => coPset_disjR).

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition my_mutexes `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (th : thread_idT) (E : coPset_disj) : mpred :=
    own γ (discrete_fun_singleton th E : cmraR).

  (** The pool reserves the full set for each thread not yet registered. *)
  Definition reserve (M : gset thread_idT) : cmraR :=
    fun th => if decide (th ∈ M) then ε else CoPset ⊤.

  Definition mutex_set_map `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (M : gset thread_idT) : mpred :=
    own γ (reserve M).

  #[global] Instance mutex_set_map_timeless `{Σ : cpp_logic, !G Σ} γ M :
    Timeless (mutex_set_map γ M).
  Proof. rewrite /mutex_set_map. apply _. Qed.
  #[global] Instance my_mutexes_timeless `{Σ : cpp_logic, !G Σ} γ th E :
    Timeless (my_mutexes γ th E).
  Proof. rewrite /my_mutexes. apply _. Qed.

  #[global] Instance mutex_set_map_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ M :
    WeaklyObjective (mutex_set_map γ M).
  Proof. rewrite /mutex_set_map. apply _. Qed.
  #[global] Instance my_mutexes_WeaklyObjective `{Σ : cpp_logic, !G Σ} γ th E :
    WeaklyObjective (my_mutexes γ th E).
  Proof. rewrite /my_mutexes. apply _. Qed.

  Section theory.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma my_mutexes_exclusive γ th (E1 E2 : coPset) :
      E1 ∩ E2 <> ∅ ->
      my_mutexes γ th (CoPset E1) **
      my_mutexes γ th (CoPset E2) |-- False.
    Proof.
      rewrite /my_mutexes.
      iIntros (Hoverlap) "[H1 H2]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
      iPureIntro.
      specialize (Hvalid th).
      rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton in Hvalid.
      rewrite coPset_disj_valid_op in Hvalid.
      set_solver.
    Qed.

    Lemma alloc_mutex_set_map :
      ⊢ |==> ∃ γ, mutex_set_map γ ∅.
    Proof.
      iMod (own_alloc (reserve ∅)) as (γ) "Hmap".
      { intros th. rewrite /reserve. case_decide; done. }
      iModIntro. iExists γ. iExact "Hmap".
    Qed.

    Lemma mutex_sets_alloc_thread γ T th :
      th ∉ T ->
      mutex_set_map γ T |--
        (|==> mutex_set_map γ (T ∪ {[th]}) **
                my_mutexes γ th (CoPset ⊤)).
    Proof.
      rewrite /mutex_set_map /my_mutexes.
      iIntros (Hfresh) "Hmap".
      iMod (own_update γ _ (reserve (T ∪ {[th]}) ⋅
        discrete_fun_singleton th (CoPset ⊤))
        with "Hmap") as "[Hmap Ht]".
      { apply discrete_fun_update. intros th'.
        rewrite discrete_fun_lookup_op.
        destruct (decide (th = th')) as [<-|Hne].
        - rewrite discrete_fun_lookup_singleton /reserve.
          rewrite decide_False; last done.
          rewrite decide_True; last set_solver.
          by rewrite left_id.
        - rewrite discrete_fun_lookup_singleton_ne; last done.
          rewrite right_id /reserve.
          destruct (decide (th' ∈ T)).
          + rewrite !decide_True; try set_solver.
          + rewrite !decide_False; try set_solver.
      }
      iModIntro. iFrame.
    Qed.

    Lemma my_mutexes_alloc_mutex_name γ th (E N : coPset) :
      N ⊆ E ->
      my_mutexes γ th (CoPset E) |--
        my_mutexes γ th (CoPset (E \ N)) ** my_mutexes γ th (CoPset N).
    Proof.
      intros Hsub.
      rewrite /my_mutexes -own_op discrete_fun_singleton_op.
      rewrite coPset_disj_union; last set_solver.
      rewrite difference_union_L.
      have -> : E ∪ N = E by set_solver.
      done.
    Qed.

  End theory.

  (* an example that two threads can allocate the same namespace token. *)
  Lemma my_mutexes_alloc_eg : forall `{Σ : cpp_logic, !G Σ}
      (th1 th2 : thread_idT) (N : coPset),
    th1 ≠ th2 ->
    ⊢ |==> ∃ γ,
      my_mutexes γ th1 (CoPset N) **
      my_mutexes γ th2 (CoPset N) **
      (mutex_set_map γ {[th1; th2]} **
       my_mutexes γ th1 (CoPset (⊤ \ N)) **
       my_mutexes γ th2 (CoPset (⊤ \ N))).
  Proof.
    intros until N. intros Hneq.
    iMod alloc_mutex_set_map as (γ) "Hmap".
    iMod (mutex_sets_alloc_thread γ ∅ th1 ltac:(set_solver)
      with "Hmap") as "[Hmap Ht1]".
    iEval (rewrite left_id_L) in "Hmap".
    iMod (mutex_sets_alloc_thread γ {[th1]} th2 ltac:(set_solver)
      with "Hmap") as "[Hmap Ht2]".
    iDestruct (my_mutexes_alloc_mutex_name γ th1 ⊤ N ltac:(set_solver)
      with "Ht1") as "[Hr1 Hn1]".
    iDestruct (my_mutexes_alloc_mutex_name γ th2 ⊤ N ltac:(set_solver)
      with "Ht2") as "[Hr2 Hn2]".
    iModIntro. iExists γ. iFrame.
  Qed.

  #[global] Hint Opaque mutex_set_map my_mutexes : sl_opacity typeclass_instances.
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
