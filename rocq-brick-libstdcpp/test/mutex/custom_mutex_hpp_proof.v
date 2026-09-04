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

  (* Definition IR `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !recursive_mutex.lockedG Σ} (γ : gname) (q : cQp.t) : mpred :=
    ∃ x, recursive_mutex.owned_count_id_auth γ.(rec_gname) x. *)
(*
    Definition rawR `{Σ : cpp_logic, σ : genv} (owner : option thread_idT) (count : nat) : Rep :=
      structR "std::recursive_mutex" 1$m **
      _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m count. *)

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ,
      !LockState.G Σ}.

    Definition mutex_inv (this : ptr) (γ : gname) (P : mpred) : mpred :=
      ∃ b : bool,
      this ,, _field "MyMutex::m_lock" |->
        atomic.R "int" 1$m (if b then 1 else 0)%Z **
      ∃ o_owner : option thread_idT,
      LockState.owner_auth γ.(lock_state_gname).(LockState.owner_gname) o_owner **
      (if b then
        ∃ th q1 q2,
          LockState.not_locked γ.(lock_state_gname) th q1 γ.(cinv_gname) **
          MutexTokens.given_token γ.(lock_state_gname).(LockState.token_gname) q2 **
          [| (q1 + q2 = 1)%Qp |]
      else
        (* LockState.owner_auth γ.(lock_state_gname) o_owner ** *)
        P **
        (** m_owner does not concern do_lock() and do_unlock(), the actual
          implementation of mutex, and does not always equal o_owner.
          It is just a resource that one can get from the invariant. *)
        this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None **
        LockState.owner_frag γ.(lock_state_gname).(LockState.owner_gname) o_owner **
        MutexTokens.given_token γ.(lock_state_gname).(LockState.token_gname) 1%Qp).

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
            LockState.owner_frag g.(lock_state_gname).(LockState.owner_gname) (Some thr))).

    cpp.spec "MyMutex::do_unlock()" as do_unlock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre ▷P
      \pre this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
      \pre LockState.owner_frag g.(lock_state_gname).(LockState.owner_gname) (Some thr)
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

    cpp.spec "MyMutex::lock()" as lock_spec with
      (\exact Reduce
        (lock_basic_lockable (Tnamed N) (fun q gqP => IR gqP.1.1 gqP.1.2 gqP.2))).

    cpp.spec "MyMutex::unlock()" as unlock_spec with
      (\exact Reduce
        (unlock_basic_lockable (Tnamed N) (fun q gqP => IR gqP.1.1 gqP.1.2 gqP.2))).

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
      \consuming user g.(user_gname) thr
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p,, o_field σ "MyMutex::m_lock") ) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 0 \/ res = 1 |]%Z **
                          if bool_decide (res = 0) then P ** owner_token_frac g.(phys_state_gname) (Some thr) **
                            p ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
                          else user g.(user_gname) thr)
                          \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M ?]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iAuIntro1. rewrite /atomic1_acc.
      rewrite {1}/IR/mutex_inv/=; work.
      wname [cinv] "#?".
      iInv lock_namespace as "?" "Hc"; work.
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first solve_ndisj.
      work.
      1: admit. (* can and should be an AC *)
      wname [cinv] "CI".
      wname [owner_token_auth] "OA".
      wname [_ |-> atomic.R _ _ _] "FL".
      wname [_ |-> thread_idR _ _] "PF".
      wname [user _ _] "U".
      ren_hyp b bool.
      iMod "Y" as "_".
      destruct b eqn:Hb.
      - iMod ("Hc" with "[FL OA PF]") as "_".
        { iExists true. ework $usenamed=true with br_erefl. }
        iModIntro. rewrite /IR. work $usenamed=true with br_erefl.
        auto.
      - iDestruct "PF" as "(P & FO & OF)".
        iMod (owner_token_update g.(phys_state_gname) _ _ (Some thr)
          with "[$OA $OF]") as "(OA & OF)".
        iMod ("Hc" with "[FL OA U]") as "_".
        { iExists true. ework $usenamed=true with br_erefl. }
        iModIntro. rewrite /IR. work $usenamed=true with br_erefl.
        auto.
    Admitted.
    Hint Resolve do_exchange_C : sl_opacity.

    #[program]
    Definition do_store_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming P
      \consuming p ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
      \consuming owner_token_frac g.(phys_state_gname) (Some thr)
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store "int" (BASE (p ,, o_field σ "MyMutex::m_lock")) 0%Z K
      \instantiate K := (p |-> IR g q P ** user g.(user_gname) thr)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M ?]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc /=.
      rewrite {1}/IR/mutex_inv /=; work.
      wname [cinv] "#?".
      iInv lock_namespace as "?" "Hc"; work.
      ren_hyp b bool.
      iExists (if b then 1%Z else 0%Z). iFrame.
      iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Y". iNext. iIntros "FL".
      iMod "Y" as "_".
      wname [P] "P".
      wname [_ |-> thread_idR _ _] "FO".
      wname [owner_token_frac] "OF".
      wname [owner_token_auth] "OA".
      iRename "P" into "CI".
      wname [P] "RP".
      wname [_ |-> thread_idR _ _] "OwnerField".
      destruct b eqn:Hb.
      - iDestruct "FO" as (owner) "(U & ->)".
        iDestruct (observe_2 [| Some owner = Some thr |] with "OA OF")
          as %->%(inj _).
        iEval (rewrite _at_offsetR) in "FL".
        iMod ("Hc" with "[FL OA RP OwnerField OF]") as "_".
        { iNext. iExists false.
          work $usenamed=true with br_erefl.
          iExists (Some thr). iFrame. }
        iModIntro. rewrite /IR. work $usenamed=true with br_erefl.
      -
        (* TODO AUTO *)
        Fail by work $usenamed=true.
        Succeed by iStopProof; work.
        iDestruct "FO" as "?"; iDestruct "OF" as "?";
          work using owner_token_frac_excl_F.
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

    Lemma mymutex_ctor_proof : verify[source] "MyMutex::MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wname [structR] "S".
      iMod (own_alloc (● (GSet ∅ : lock_ghostUR))) as (gu) "UT".
      { apply auth_auth_valid. done. }
      iMod (own_alloc (●E None ⋅ ◯E None)) as (gp) "O".
      { apply excl_auth_valid. }
      iDestruct (own_op with "O") as "(OA & OF)".
      iMod (cinv_alloc ⊤ lock_namespace
        (mutex_inv this (MkGname gu gu gp) P) with "[-S UT]")
        as (gi) "(#CI & CO)"; last first.
      - iExists (MkGname gu gi gp).
        rewrite /IR used_threads.unlock /=.
        iModIntro. go $usenamed=true with br_erefl.
      - rewrite /mutex_inv owner_token_auth.unlock
          owner_token_frac.unlock /=.
        iNext. iExists false. iFrame.
    Qed.

    Lemma mymutex_dtor_proof : verify[source] "MyMutex::~MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite /IR /mutex_inv.
      work.
      wname [cinv] "#CI".
      wname [cinv_own] "CO".
      iMod (cinv_cancel with "CI CO")
        as "Inv"; [done..|].
      go.
      iDestruct "Inv" as (b) "(Lock & % & OA & State)".
      destruct b eqn:Hb.
      - iDestruct "State" as (th) "(U & %Eq)".
        iDestruct (used_threads_empty_no_not_locked with "[$]") as %[].
      - iDestruct "State" as "(P & Owner & OF)".
        ego $usenamed=true with br_erefl.
        wname [used_threads] "UT".
        iApply (affine with "[OA OF UT]"); last iAccu. apply mpred_BiAffine.
  Qed.

    Lemma mymutex_lock_proof : verify[source] "MyMutex::lock()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite locked.unlock.
      ego.
    Qed.

    Lemma mymutex_unlock_proof : verify[source] "MyMutex::unlock()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite locked.unlock.
      (* TODO AUTO *)
      Fail by ego.
      repeat (go; ework).
    Qed.


  End with_Σ.
End custom_mutex.
