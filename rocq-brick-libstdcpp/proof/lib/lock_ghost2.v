Require Import iris.algebra.agree.
Require Import iris.algebra.frac.
Require Import iris.algebra.gmap.
Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.
Require Import iris.algebra.lib.gmap_view.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Import linearity.

(** The mutex specification depends on the ghost state through these
    interfaces. *)

Module Type MUTEX_SETS.
  Parameter cmraR : cmra.

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Parameter my_mutexes : forall `{Σ : cpp_logic, !G Σ},
    namespace -> iprop.gname -> thread_idT -> gset iprop.gname -> mpred.

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

  Parameter alloc : forall `{Σ : cpp_logic, !G Σ},
    ⊢ |==> ∃ γ, token γ 1 ** given_token γ 1.
End MUTEX_TOKENS.

Module Type MUTEX_STATE.
  Declare Module Sets : MUTEX_SETS.
  Declare Module Tokens : MUTEX_TOKENS.
  Parameter owner_cmraR : cmra.

  Parameter gname : Set.

  Class G `{Σ : cpp_logic} := {
    #[global] sets_G :: Sets.G Σ;
    #[global] tokens_G :: Tokens.G Σ;
    #[local] has_owner :: HasOwn (iPropI _Σ) owner_cmraR;
    #[local] has_owner_upd :: HasOwnUpd (iPropI _Σ) owner_cmraR;
    #[local] has_owner_valid :: HasOwnValid (iPropI _Σ) owner_cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Parameter owner_auth : forall `{Σ : cpp_logic, !G Σ},
    gname -> option thread_idT -> mpred.
  Parameter owner_frag : forall `{Σ : cpp_logic, !G Σ},
    gname -> option thread_idT -> mpred.

  #[global] Declare Instance owner_auth_timeless
      `{Σ : cpp_logic, !G Σ} γ o_thr : Timeless (owner_auth γ o_thr).
  #[global] Declare Instance owner_frag_timeless
      `{Σ : cpp_logic, !G Σ} γ o_thr : Timeless (owner_frag γ o_thr).
  #[global] Declare Instance owner_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_frag γ).

  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    gname -> Qp -> mpred.
  Parameter not_locked : forall `{Σ : cpp_logic, !G Σ},
    gname -> thread_idT -> Qp -> iprop.gname -> mpred.
  Parameter locked : forall `{Σ : cpp_logic, !G Σ},
    gname -> option thread_idT -> Qp -> mpred.

  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  #[global] Declare Instance locked_timeless
      `{Σ : cpp_logic, !G Σ} γ th q : Timeless (locked γ th q).
  #[global] Declare Instance locked_exclusive
      `{Σ : cpp_logic, !G Σ} γ q : Exclusive1 (fun th => locked γ th q).
End MUTEX_STATE.

(** ** Exact per-thread mutex sets *)

Module MutexSets.
  Canonical Structure cmraR : cmra :=
    gmap_viewR thread_idT (agreeR (leibnizO (gset iprop.gname))).

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition mutex_sets_view
      (M : gmap thread_idT (gset iprop.gname)) :
      gmap thread_idT (agree (leibnizO (gset iprop.gname))) :=
    (λ X : gset iprop.gname, to_agree X) <$> M.

  sl.lock
  Definition mutex_sets_auth `{Σ : cpp_logic, !G Σ}
      (γpool : iprop.gname)
      (M : gmap thread_idT (gset iprop.gname)) : mpred :=
    own γpool (gmap_view_auth (DfracOwn 1) (mutex_sets_view M)).

  sl.lock
  Definition mutex_sets_frag `{Σ : cpp_logic, !G Σ}
      (γpool : iprop.gname) (th : thread_idT)
      (M : gset iprop.gname) : mpred :=
    own γpool
      (gmap_view_frag
        (V := agreeR (leibnizO (gset iprop.gname)))
        th (DfracOwn 1) (to_agree M)).

  sl.lock
  Definition my_mutexes_inv `{Σ : cpp_logic, !G Σ}
      (γpool : iprop.gname) : mpred :=
    ∃ M : gmap thread_idT (gset iprop.gname), mutex_sets_auth γpool M.

  Definition my_mutexes `{Σ : cpp_logic, !G Σ}
      (N : namespace) (γpool : iprop.gname) (th : thread_idT)
      (M : gset iprop.gname) : mpred :=
    inv N (my_mutexes_inv γpool) ** mutex_sets_frag γpool th M.

  #[only(timeless)] derive mutex_sets_auth.
  #[only(timeless)] derive mutex_sets_frag.
  #[only(timeless)] derive my_mutexes_inv.

  #[global] Instance my_mutexes_inv_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γpool :
    WeaklyObjective (my_mutexes_inv γpool).
  Proof.
      rewrite my_mutexes_inv.unlock mutex_sets_auth.unlock. apply _.
  Qed.

  Section theory.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma mutex_sets_frag_exclusive γpool th M1 M2 :
      mutex_sets_frag γpool th M1 ** mutex_sets_frag γpool th M2 |-- False.
    Proof.
      rewrite mutex_sets_frag.unlock.
      iIntros "[H1 H2]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
      apply gmap_view_frag_op_valid in Hvalid as [Hfrac _].
      rewrite dfrac_op_own dfrac_valid_own in Hfrac.
      exfalso. exact (Qp.not_add_le_l 1 1 Hfrac).
    Qed.

    Lemma mutex_sets_update γpool M th S S' :
      mutex_sets_auth γpool M ** mutex_sets_frag γpool th S |--
        (|==> mutex_sets_auth γpool (<[th := S']> M) **
               mutex_sets_frag γpool th S').
    Proof.
      rewrite mutex_sets_auth.unlock mutex_sets_frag.unlock
        /mutex_sets_view fmap_insert.
      iIntros "[HA HF]".
      iMod (own_update_2 with "HA HF") as "[HA HF]".
      { apply (gmap_view_replace
          (V := agreeR (leibnizO (gset iprop.gname)))
          (mutex_sets_view M) th (to_agree S) (to_agree S')). done. }
      iModIntro. iFrame.
    Qed.

    Lemma mutex_sets_alloc_thread γpool M th :
      M !! th = None ->
      mutex_sets_auth γpool M |--
        (|==> mutex_sets_auth γpool (<[th := ∅]> M) **
               mutex_sets_frag γpool th ∅).
    Proof.
      rewrite mutex_sets_auth.unlock mutex_sets_frag.unlock
        /mutex_sets_view fmap_insert.
      iIntros (Hfresh) "HA".
      iMod (own_update with "HA") as "[HA HF]".
      { apply (gmap_view_alloc
          (V := agreeR (leibnizO (gset iprop.gname)))
          (mutex_sets_view M) th (DfracOwn 1) (to_agree ∅)).
        - rewrite lookup_fmap Hfresh. done.
        - done.
        - done. }
      iModIntro. iFrame.
    Qed.

    Lemma my_mutexes_exclusive N1 N2 γpool th M1 M2 :
      my_mutexes N1 γpool th M1 ** my_mutexes N2 γpool th M2 |-- False.
    Proof.
      rewrite /my_mutexes.
      iIntros "[[_ H1] [_ H2]]".
      iApply (mutex_sets_frag_exclusive with "[$H1 $H2]").
    Qed.

    Lemma my_mutexes_alloc N th :
      ⊢ |={⊤}=> ∃ γpool, my_mutexes N γpool th ∅.
    Proof.
      iMod (own_alloc
        (gmap_view_auth
          (V := agreeR (leibnizO (gset iprop.gname)))
          (DfracOwn 1) (mutex_sets_view ∅))) as (γpool) "HA".
      { apply gmap_view_auth_valid. }
      iAssert (mutex_sets_auth γpool ∅) with "[HA]" as "Hauth".
      { rewrite mutex_sets_auth.unlock. iExact "HA". }
      have Hfresh :
          (∅ : gmap thread_idT (gset iprop.gname)) !! th = None by done.
      iMod (mutex_sets_alloc_thread γpool ∅ th Hfresh with "Hauth")
        as "[HA HF]".
      iMod (inv_alloc N _ (my_mutexes_inv γpool) with "[HA]") as "#Hinv".
      { iNext. rewrite my_mutexes_inv.unlock.
        iExists ({[th := ∅]} : gmap thread_idT (gset iprop.gname)).
        iFrame. }
      iModIntro. iExists γpool. rewrite /my_mutexes. iFrame.
      Unshelve. all: try done.
    Qed.

    Lemma my_mutexes_insert N γpool th M g :
      my_mutexes N γpool th M |--
        (|={⊤}=> my_mutexes N γpool th (M ∪ {[g]})).
    Proof.
      rewrite /my_mutexes.
      iIntros "[#Hinv HF]".
      iInv N as "Hpool" "Hclose".
      rewrite my_mutexes_inv.unlock.
      iDestruct "Hpool" as (A) ">HA".
      iMod (mutex_sets_update γpool A th M (M ∪ {[g]})
        with "[$HA $HF]") as "[HA HF]".
      iMod ("Hclose" with "[HA]") as "_".
      { iNext. iExists _. iFrame. }
      iModIntro. iFrame "Hinv HF".
    Qed.
  End theory.
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

  Section theory.
    Context `{Σ : cpp_logic, !G Σ}.

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
    (Tokens0 : MUTEX_TOKENS) : MUTEX_STATE.
  Module Sets := Sets0.
  Module Tokens := Tokens0.

  #[local] Existing Instance Tokens.token_fractional.
  #[local] Existing Instance Tokens.given_token_fractional.
  #[local] Existing Instance Tokens.token_timeless.
  #[local] Existing Instance Tokens.given_token_timeless.

  Canonical Structure owner_cmraR : cmra :=
    excl_authR (optionO thread_idTO).

  Record mutex_gname : Set := MkGname {
    pool_namespace : namespace;
    pool_gname : iprop.gname;
    token_gname : iprop.gname;
    owner_gname : iprop.gname;
  }.
  Definition gname : Set := mutex_gname.

  Class G `{Σ : cpp_logic} := {
    #[global] sets_G :: Sets.G Σ;
    #[global] tokens_G :: Tokens.G Σ;
    #[local] has_owner :: HasOwn (iPropI _Σ) owner_cmraR;
    #[local] has_owner_upd :: HasOwnUpd (iPropI _Σ) owner_cmraR;
    #[local] has_owner_valid :: HasOwnValid (iPropI _Σ) owner_cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition owner_auth `{Σ : cpp_logic, !G Σ}
      (γ : gname) (o_thr : option thread_idT) : mpred :=
    own γ.(owner_gname) ((●E o_thr) : owner_cmraR).

  Definition owner_frag `{Σ : cpp_logic, !G Σ}
      (γ : gname) (o_thr : option thread_idT) : mpred :=
    own γ.(owner_gname) ((◯E o_thr) : owner_cmraR).

  #[global] Hint Opaque owner_auth owner_frag : sl_opacity typeclass_instances.

  #[only(timeless)] derive owner_auth.
  #[only(timeless)] derive owner_frag.

  #[global] Instance owner_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_frag γ).
  Proof.
    intros o_thr1 o_thr2. rewrite /owner_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid. rewrite excl_auth_frag_op_valid. done.
  Qed.

  Definition token `{Σ : cpp_logic, !G Σ}
      (γ : gname) (q : Qp) : mpred :=
    Tokens.token γ.(token_gname) q.

  Definition not_locked `{Σ : cpp_logic, !G Σ}
      (γ : gname) (th : thread_idT) (q : Qp) 
      (inv_gname : iprop.gname) : mpred :=
    Sets.my_mutexes
      γ.(pool_namespace) γ.(pool_gname) th {[inv_gname]} **
    Tokens.token γ.(token_gname) q.

  Definition locked `{Σ : cpp_logic, !G Σ}
      (γ : gname) (o_thr : option thread_idT) (q : Qp) : mpred :=
    Tokens.given_token γ.(token_gname) q **
    owner_frag γ o_thr.

  Lemma not_locked_eq `{Σ : cpp_logic, !G Σ} γ th q inv_gname :
    not_locked γ th q inv_gname ⊣⊢
      Sets.my_mutexes
        γ.(pool_namespace) γ.(pool_gname) th
        {[inv_gname]} **
      Tokens.token γ.(token_gname) q.
  Proof. done. Qed.

  Lemma locked_eq `{Σ : cpp_logic, !G Σ} γ o_thr q :
    locked γ o_thr q ⊣⊢
      Tokens.given_token γ.(token_gname) q **
      owner_frag γ o_thr.
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

End MakeMutexState.

Module LockState := MakeMutexState MutexSets MutexTokens.
