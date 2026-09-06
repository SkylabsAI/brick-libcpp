(** Provisional *)

Require Import iris.algebra.lib.excl_auth.
Require Import iris.algebra.gset.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.base_derived.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.atomic.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Import linearity.
Require Import skylabs.brick.libstdcpp.test.mutex.custom_mutex_hpp.
Module custom_mutex.

  Abbreviation N := "MyMutex"%cpp_name.

  (* FIXME maybe don't need to split it? *)
  Parameter thread_idR : ∀ `{Σ : cpp_logic, σ : genv}, cQp.t ->
    (* None if value is thread::id(), Some otherwise *)
    option thread_idT -> Rep.
  #[only(cfracsplittable, type_ptr="std::thread::id")] derive thread_idR.
  #[global] Axiom thread_idR_WeaklyObjective :
    ∀ `{Σ : cpp_logic, σ : genv} (q : cQp.t)
      (o : option thread_idT) (p : ptr),
      WeaklyObjective (thread_idR q o p).
  #[global] Existing Instance thread_idR_WeaklyObjective.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
    WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.

  Record gname : Set := MkGname
  { lock_state_gname : LockState.gname
  ; cinv_gname : iprop.gname
  }.

  Definition lock_namespace : namespace := nroot .@@ "MyMutex".

  sl.lock
  Definition locked `{Σ : cpp_logic} `{!LockState.G Σ} `{σ : genv}
      (γ: gname) (thr : thread_idT) (q : cQp.t) : Rep :=
    _field "MyMutex::m_owner" |-> thread_idR 1$m (Some thr) ** pureR (LockState.locked γ.(lock_state_gname) (Some thr) q%Qp).
  #[global] Hint Opaque locked : sl_opacity typeclass_instances.
  #[only(timeless, exclusive)] derive locked.

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ,
      !LockState.G Σ}.

    (** The invariant holds the thread's mutex set while the spinlock is held.
        Its token balance supports both full and partial ownership transfers. *)
    Definition mutex_inv (this : ptr) (γ : gname) (P : mpred) : mpred :=
      ∃ b : bool,
      this ,, _field "MyMutex::m_lock" |->
        atomic.R "int" 1$m (if b then 1 else 0)%Z **
      ∃ o_owner : option thread_idT,
      LockState.owner_tid_auth γ.(lock_state_gname) o_owner **
      (if b then
        ∃ th,
          MutexSets.my_mutexes
            γ.(lock_state_gname).(LockState.pool_namespace)
            γ.(lock_state_gname).(LockState.pool_gname) th {[γ.(cinv_gname)]} **
          [| o_owner = Some th |] **
          MutexTokens.token_not_full γ.(lock_state_gname).(LockState.token_gname)
      else
        P **
        (** The physical owner is cleared before [do_unlock]; the ghost owner
            records the last acquiring thread until the next acquisition. *)
        this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None **
        LockState.owner_tid_frag γ.(lock_state_gname) o_owner **
        MutexTokens.token_full γ.(lock_state_gname).(LockState.token_gname)).

    Definition IR (γ : gname) (q : cQp.t) (P : mpred) : Rep :=
      structR N q$m **
      as_Rep (fun this =>
        cinv lock_namespace γ.(cinv_gname) (mutex_inv this γ P) **
        cinv_own γ.(cinv_gname) q
      ).
    Hint Opaque IR : sl_opacity typeclass_instances.
    #[only(type_ptr,cfractional,ascfractional,cfracvalid)] derive IR.

    Context `{MOD : source ⊧ σ}.

    Abbreviation GLOBALS q :=
      (_global "std::memory_order_seq_cst" |->
        primR "enum std::memory_order" q
          (memory_order.to_val memory_order.seq_cst)).

    cpp.spec (default_ctor "std::thread::id") as thread_id_ctor_spec with (
      \this this
      \post this |-> thread_idR 1$m None).

    cpp.spec (const_copy_ctor "std::thread::id") as thread_id_copy_ctor_spec with (
      \this this
      \arg{other} "" (Vptr other)
      \prepost{q o} other |-> thread_idR q o
      \post this |-> thread_idR 1$m o).

    cpp.spec (dtor "std::thread::id") as thread_id_dtor_spec with (
      \this this
      \pre{o} this |-> thread_idR 1$m o
      \post emp).

    cpp.spec "std::thread::id::operator=(const std::thread::id&)"
        as thread_id_copy_assign_spec with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{old} this |-> thread_idR 1$m old
      \prepost{q o} other |-> thread_idR q o
      \post[Vref this] this |-> thread_idR 1$m o).

    cpp.spec "std::thread::id::operator=(std::thread::id&&)"
        as thread_id_move_assign_spec with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{old} this |-> thread_idR 1$m old
      \prepost{o} other |-> thread_idR 1$m o
      \post[Vref this] this |-> thread_idR 1$m o).

    cpp.spec "std::operator==(std::thread::id, std::thread::id)"
        as thread_id_eq_spec with (
      \arg{lhs} "" (Vptr lhs)
      \arg{rhs} "" (Vptr rhs)
      \prepost{q1 o1} lhs |-> thread_idR q1 o1
      \prepost{q2 o2} rhs |-> thread_idR q2 o2
      \post[Vbool (bool_decide (o1 = o2))] emp).

    cpp.spec "std::this_thread::get_id()" as get_id_spec with (
      \persist{thr} current_thread thr
      \post{result}[Vptr result]
        result |-> thread_idR 1$m (Some thr)).

    cpp.spec "MyMutex::MyMutex()" as ctor_spec with (
      \this this
      \pre{P} ▷P
      \require WeaklyObjective P
      \post (|={⊤}=> Exists g,
        this |-> IR g 1$m P ** LockState.token g.(lock_state_gname) 1%Qp)).

    cpp.spec "MyMutex::~MyMutex()" as dtor_spec with (
      \this this
      \pre{g P} this |-> IR g 1$m P ** LockState.token g.(lock_state_gname) 1%Qp
      \post P).

    cpp.spec "MyMutex::do_lock()" as do_lock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname)
      \prepost{q'} GLOBALS q'
      (* does not have to be q, but easier if it is *)
      \post (P **
            this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None **
            LockState.locked g.(lock_state_gname) (Some thr) q)).

    cpp.spec "MyMutex::do_unlock()" as do_unlock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre ▷P
      \pre this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
      \pre LockState.locked g.(lock_state_gname) (Some thr) q
      \post LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname)).

    Definition T : Type := gname * cQp.t * mpred.

    Definition do_lock (this : ptr) (lk : T) (K : mpred) : mpred :=
      let g := lk.1.1 in
      let q := lk.1.2 in
      let P := lk.2 in
      ∃ thr q', current_thread thr **
        LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname) **
        GLOBALS q' **
        (GLOBALS q' ** P ** this |-> locked g thr q -* K).
    #[global] Arguments do_lock /.

    Definition do_unlock (this : ptr) (lk : T) (K : mpred) : mpred :=
      let g := lk.1.1 in
      let q := lk.1.2 in
      let P := lk.2 in
      ∃ thr , current_thread thr ** this |-> locked g thr q ** ▷P **
        (LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname) -* K).
    #[global] Arguments do_unlock /.

    #[global] Instance custom_mutex_basic_lockable :
        BasicLockable (T := T) (Tnamed N)
          (fun _ gqP => IR gqP.1.1 gqP.1.2 gqP.2) :=
      { do_lock := do_lock
      ; do_unlock := do_unlock }.

    cpp.spec "MyMutex::lock()" as lock_spec_alt with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname)
      \prepost{q'} GLOBALS q'
      \post P ** this |-> locked g thr q).

    cpp.spec "MyMutex::unlock()" as unlock_spec_alt with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre this |-> locked g thr q ** ▷P
      \post LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname)).

    cpp.spec "MyMutex::lock()" as lock_spec with
      (\exact Reduce
        (lock_basic_lockable (Tnamed N) (fun q gqP => IR gqP.1.1 gqP.1.2 gqP.2))).

    cpp.spec "MyMutex::unlock()" as unlock_spec with
      (\exact Reduce
        (unlock_basic_lockable (Tnamed N) (fun q gqP => IR gqP.1.1 gqP.1.2 gqP.2))).

    Lemma lock_spec_entails_lock_spec_alt : lock_spec -|- lock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; ework with br_erefl.
      lazymatch goal with
      | |- environments.envs_entails _ ?Ggoal =>
        lazymatch Ggoal with
        | context[IR ?gqP.1.1 ?gqP.1.2 ?gqP.2] => unify gqP (g, q, P)
        end
      end.
      ework with br_erefl.
      Unshelve. all: exact (1$m)%cQp.
    Qed.

    Lemma unlock_spec_entails_unlock_spec_alt : unlock_spec -|- unlock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; ework with br_erefl.
      lazymatch goal with
      | |- environments.envs_entails _ ?Ggoal =>
        lazymatch Ggoal with
        | context[IR ?gqP.1.1 ?gqP.1.2 ?gqP.2] => unify gqP (g, q, P)
        end
      end.
      ework with br_erefl.
      Unshelve. all: exact (1$m)%cQp.
    Qed.

    cpp.spec "std::this_thread::yield()" as yield_spec with (
      \post emp).

    Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

    Definition bi_later_exist_F := [FWD] @bi.later_exist.
    Definition bi_later_sep_F := [FWD] @bi.later_sep.
    Definition bi_later_sep_B := [BWD->] @bi.later_sep.
    Hint Resolve bi_later_exist_F bi_later_sep_F : br_hints.
    Import linearity.

    #[program]
    Definition do_exchange_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname)
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p,, o_field σ "MyMutex::m_lock") ) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 0 \/ res = 1 |]%Z **
                          if bool_decide (res = 0) then P ** LockState.locked g.(lock_state_gname) (Some thr) q **
                            p ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
                          else LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname))
                          \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & NL)".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv lock_namespace as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (b) "[>L Inv]".
      iDestruct "Inv" as (oo) "[>OA State]".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if b then 1 else 0)%Z.
      iSplitL "L".
      { ework $usenamed=true with br_erefl. }
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L OA State]") as "_".
        { iNext. rewrite /mutex_inv. iExists b.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iExists oo. iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros "L". iMod "Y" as "_".
        destruct b.
        + iMod ("Hclose" with "[L OA State]") as "_".
          { iNext. rewrite /mutex_inv. iExists true.
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iExists oo. iFrame. }
          iModIntro. rewrite /IR _at_sep _at_as_Rep /=.
          iFrame "CI". iFrame. iPureIntro. auto.
        + iDestruct "State" as "(P & Owner & OF & Balance)".
          iEval (rewrite /LockState.not_locked /LockState.token) in "NL".
          iDestruct "NL" as "[Sets T]".
          iDestruct (MutexTokens.acquire with "[$Balance $T]") as "[GT Balance]".
          iMod (LockState.owner_update _ _ _ (Some thr) with "[$OA $OF]")
            as "[OA OF]".
          iMod ("Hclose" with "[L OA Sets Balance]") as "_".
          { iNext. rewrite /mutex_inv. iExists true.
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iExists (Some thr). iFrame "OA".
            iExists thr. iFrame. done. }
          iModIntro. rewrite /IR _at_sep _at_as_Rep /LockState.locked /=.
          iFrame "CI". iFrame. iPureIntro. auto.
    Qed.
    Hint Resolve do_exchange_C : sl_opacity.

    #[program]
    Definition do_store_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming P
      \consuming p ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
      \consuming LockState.locked g.(lock_state_gname) (Some thr) q
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store "int" (BASE (p ,, o_field σ "MyMutex::m_lock")) 0%Z K
      \instantiate K := (p |-> IR g q P ** LockState.not_locked g.(lock_state_gname) thr q g.(cinv_gname))
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & P & Owner & Locked)".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      iEval (rewrite /LockState.locked) in "Locked".
      iDestruct "Locked" as "[GT OF]".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc /=.
      iInv lock_namespace as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (b) "[>L Inv]".
      iDestruct "Inv" as (oo) "[>OA State]".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if b then 1 else 0)%Z.
      iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      destruct b.
      - iDestruct "State" as (owner) "(Sets & %Heq & Balance)".
        iDestruct (observe_2 [| oo = Some thr |] with "OA OF") as %Howner.
        have -> : owner = thr by congruence.
        iDestruct (MutexTokens.release with "[$Balance $GT]") as "[T Balance]".
        iMod ("Hclose" with "[L OA P Owner OF Balance]") as "_".
        { iNext. rewrite /mutex_inv. iExists false.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iExists oo. iFrame. by rewrite Howner. }
        iModIntro.
        rewrite /IR _at_sep _at_as_Rep /LockState.not_locked /=.
        iFrame "CI". iFrame.
      - iDestruct "State" as "(P0 & Owner0 & OF0 & Balance0)".
        iDestruct (LockState.owner_tid_frag_exclusive with "OF0 OF") as %[].
    Qed.
    Hint Resolve do_store_C : sl_opacity.

    #[program]
    Definition do_load_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{q (n : Z)} p |-> atomic.R "int" q n
      \proving{(K : Z -> mpred) (_ : IsExistential K)}
        std.atomic.do_load "int" (BASE p) K
      \instantiate K :=
        (fun x : Z => p |-> atomic.R "int" q n ** [| x = n |])
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M ?]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      rewrite /std.atomic.do_load.
      iAcIntro. rewrite /commit_acc.
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
      work. iExists q. work.
      iMod "Y". iModIntro.
      work.
    Qed.
    Hint Resolve do_load_C : sl_opacity.

    Hint Opaque locked : sl_opacity.

    Lemma mymutex_do_lock_proof : verify[source] "MyMutex::do_lock()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wp_while (fun _ => emp); go; first by ework.
      wp_if; go.
    Qed.

    Lemma mymutex_do_unlock_proof : verify[source] "MyMutex::do_unlock()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
    Qed.

    Lemma mymutex_lock_alt_proof : verify[source] lock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
      rewrite locked.unlock.
      ego.
    Qed.

    Lemma mymutex_unlock_alt_proof : verify[source] unlock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite locked.unlock.
      repeat (go; ework).
    Qed.

    Lemma mymutex_ctor_proof : verify[source] "MyMutex::MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wname [structR] "S".
      wname [P] "P".
      wname [_ |-> atomic.R _ _ _] "L".
      wname [_ |-> thread_idR _ _] "Owner".
      iMod (MutexSets.alloc_pool (nroot .@@ "MyMutexPool")) as (gp) "#Pool".
      iMod (MutexTokens.alloc) as (gt) "[T GT]".
      iMod (own_alloc ((●E None ⋅ ◯E None) : LockState.owner_cmraR)) as (go) "O".
      { apply excl_auth_valid. }
      iDestruct (own_op with "O") as "[OA OF]".
      pose (gs := LockState.MkGname (nroot .@@ "MyMutexPool") gp gt go).
      iMod (cinv_alloc_cofinite ∅ ⊤ lock_namespace) as (gi) "(_ & CO & Halloc)".
      iMod ("Halloc" $! (mutex_inv this (MkGname gs gi) P)
        with "[] [L P Owner OA OF GT]") as "#CI".
      { iPureIntro. rewrite /mutex_inv. apply _. }
      { iNext. rewrite /mutex_inv /=. iExists false. iFrame "L".
        iExists None. rewrite /LockState.owner_tid_auth /LockState.owner_tid_frag /gs /=.
        iFrame. rewrite /MutexTokens.token_full. iLeft. iExact "GT". }
      iModIntro. iExists (MkGname gs gi).
      rewrite /IR _at_sep _at_as_Rep /LockState.token /gs /=.
      iFrame "CI". iFrame.
    Qed.

    Lemma mymutex_dtor_proof : verify[source] "MyMutex::~MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite /IR /mutex_inv.
      work.
      wname [cinv] "#CI".
      wname [cinv_own] "CO".
      wname [LockState.token] "T".
      iMod (cinv_cancel with "CI CO")
        as "Inv"; [done..|].
      go.
      iDestruct "Inv" as (b) "(Lock & % & OA & State)".
      destruct b eqn:Hb.
      - iDestruct "State" as (th) "(Sets & %Eq & Balance)".
        iEval (rewrite /LockState.token) in "T".
        iDestruct (MutexTokens.token_not_full_full_token with "[$Balance $T]") as %[].
      - iDestruct "State" as "(P & Owner & OF & Balance)".
        ego $usenamed=true with br_erefl.
        iApply (affine with "[OA OF Balance T]"); last iAccu. apply mpred_BiAffine.
    Qed.

    Lemma mymutex_lock_proof : verify[source] lock_spec.
    Proof using MOD HAS_THREADS.
      rewrite lock_spec_entails_lock_spec_alt.
      exact mymutex_lock_alt_proof.
    Qed.

    Lemma mymutex_unlock_proof : verify[source] unlock_spec.
    Proof using MOD HAS_THREADS.
      rewrite unlock_spec_entails_unlock_spec_alt.
      exact mymutex_unlock_alt_proof.
    Qed.


  End with_Σ.
End custom_mutex.
