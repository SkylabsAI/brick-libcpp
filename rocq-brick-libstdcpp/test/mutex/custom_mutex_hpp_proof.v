(** Provisional *)

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

(** The ghost implementation and its physical client predicates are specific
    to [MyMutex]. The entire mutex-set pool still uses one shared ghost name. *)
Module CustomMutexState (Sets0 : MUTEX_SETS) (Tokens0 : MUTEX_TOKENS)
    (Owners0 : OWNER_TID) <: MUTEX_PREDS.
  Record mutex_gname : Set := MkGname {
    pool_gname : iprop.gname;
    invariant_gname : iprop.gname;
    token_gname : iprop.gname;
    owner_gname : iprop.gname;
  }.
  Definition gname : Set := mutex_gname.
  Definition pool_name (γ : gname) : iprop.gname := γ.(pool_gname).

  Class stateG `{Σ : cpp_logic} := {
    #[global] sets_G :: Sets0.G Σ;
    #[global] tokens_G :: Tokens0.G Σ;
    #[global] owners_G :: Owners0.G Σ;
  }.
  Definition G := @stateG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance state_G `{Σ : cpp_logic} (H : G Σ) : @stateG _ _ Σ := H.

  Definition token `{Σ : cpp_logic, !G Σ}
      (γ : gname) (q : cQp.t) : mpred :=
    Tokens0.token γ.(token_gname) q.

  Definition not_locked_ghost `{Σ : cpp_logic, !G Σ}
      (γ : mutex_gname) (th : thread_idT) (q : Qp) : mpred :=
    Sets0.mutex_set_frag γ.(pool_gname) th (GSet {[γ.(invariant_gname)]}) **
    Tokens0.token γ.(token_gname) q.

  Definition owner_token `{Σ : cpp_logic, !G Σ}
      (γ : mutex_gname) (th : thread_idT) (q : Qp) : mpred :=
    Tokens0.given_token γ.(token_gname) q **
    Owners0.owner_tid_frag γ.(owner_gname) (Some th).

  #[global] Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : CFractional (token γ).
  Proof.
    intros q1 q2. rewrite /token cQp.frac_add.
    apply Tokens0.token_fractional.
  Qed.

  #[global] Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  Proof. rewrite /token. apply _. Qed.

  #[global] Instance owner_token_timeless
      `{Σ : cpp_logic, !G Σ} γ th q : Timeless (owner_token γ th q).
  Proof. rewrite /owner_token. apply _. Qed.

  #[global] Instance owner_token_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive2 (owner_token γ).
  Proof.
    intros th1 th2 q1 q2. rewrite /owner_token.
    apply observe_2_sep_r. apply _.
  Qed.

  (** While held, the invariant owns this thread's singleton mutex fragment
      and the token balance. The thread retains its mutex-set authority.
      When free, both halves of the previous owner remain in the invariant. *)
  Definition state `{Σ : cpp_logic, !G Σ}
      (γ : mutex_gname) (b : bool) : mpred :=
    (if b then
      ∃ th, Owners0.owner_tid_auth γ.(owner_gname) (Some th) **
        Sets0.mutex_set_frag γ.(pool_gname) th (GSet {[γ.(invariant_gname)]}) **
        Tokens0.token_not_full γ.(token_gname)
    else
      ∃ owner, Owners0.owner_tid_auth γ.(owner_gname) owner **
        Owners0.owner_tid_frag γ.(owner_gname) owner **
        Tokens0.token_full γ.(token_gname))%I.

  #[global] Instance state_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ b :
    WeaklyObjective (state γ b).
  Proof. rewrite /state. destruct b; apply _. Qed.

  Section state_laws.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma alloc (γpool : iprop.gname) inv_gname :
      ⊢ |==> ∃ γ, [| γ.(pool_gname) = γpool |] ** [| γ.(invariant_gname) = inv_gname |] **
        token γ 1$m ** state γ false.
    Proof.
      iMod Tokens0.alloc as (gt) "[T GT]".
      iMod (Owners0.alloc None) as (go) "[OA OF]".
      iModIntro. iExists (MkGname γpool inv_gname gt go).
      iSplit; first done. iSplit; first done.
      rewrite /token /state /=. iFrame "T". iExists None.
      iFrame "OA OF".
      iApply Tokens0.token_full_init. iExact "GT".
    Qed.

    Lemma do_lock γ th q :
      state γ false ** not_locked_ghost γ th q |--
        (|==> state γ true ** owner_token γ th q).
    Proof.
      rewrite /state /not_locked_ghost /owner_token.
      iIntros "[State [Sets T]]".
      iDestruct "State" as (owner) "(OA & OF & Balance)".
      iDestruct (Tokens0.acquire with "[$Balance $T]") as "[GT Balance]".
      iMod (Owners0.owner_update γ.(owner_gname) _ _ (Some th)
        with "[$OA $OF]") as "[OA OF]".
      iModIntro. iFrame "GT OF". iExists th. iFrame.
    Qed.

    Lemma do_unlock γ th q :
      state γ true ** owner_token γ th q |--
        (|==> state γ false ** not_locked_ghost γ th q).
    Proof.
      rewrite /state /owner_token /not_locked_ghost.
      iIntros "[State [GT OF]]".
      iDestruct "State" as (owner) "(OA & Sets & Balance)".
      iDestruct (observe_2 [| Some owner = Some th |] with "OA OF") as %Heq.
      injection Heq as ->.
      iDestruct (Tokens0.release with "[$Balance $GT]") as "[T Balance]".
      iModIntro. iFrame "Sets T". iExists (Some th). iFrame.
    Qed.

    Lemma unlocked_owner_token γ th q :
      state γ false ** owner_token γ th q |-- False.
    Proof.
      rewrite /state /owner_token. iIntros "[State [_ OF]]".
      iDestruct "State" as (owner) "(_ & OF0 & _)".
      iDestruct (Owners0.owner_tid_frag_exclusive with "OF0 OF") as %[].
    Qed.

    Lemma locked_full_token γ :
      state γ true ** token γ 1$m |-- False.
    Proof.
      rewrite /state /token. iIntros "[State T]".
      iDestruct "State" as (th) "(_ & _ & Balance)".
      iApply (Tokens0.token_not_full_full_token with "[$Balance $T]").
    Qed.
  End state_laws.

  #[global] Hint Opaque token not_locked_ghost owner_token state : sl_opacity typeclass_instances.

  Parameter thread_idR : ∀ `{Σ : cpp_logic, σ : genv}, cQp.t ->
    (* None if value is thread::id(), Some otherwise *)
    option thread_idT -> Rep.
  #[only(cfracsplittable, type_ptr="std::thread::id")] derive thread_idR.
  #[global] Axiom thread_idR_WeaklyObjective :
    ∀ `{Σ : cpp_logic, σ : genv} (q : cQp.t)
      (o : option thread_idT) (p : ptr),
      WeaklyObjective (thread_idR q o p).
  #[global] Existing Instance thread_idR_WeaklyObjective.

  Definition globals `{Σ : cpp_logic} {σ : genv} (q : cQp.t) : mpred :=
    _global "std::memory_order_seq_cst" |->
      primR "enum std::memory_order" q
        (memory_order.to_val memory_order.seq_cst).

  Definition not_locked `{Σ : cpp_logic, !G Σ} {σ : genv}
      (this : ptr) (γ : gname) (th : thread_idT) (q : cQp.t) : mpred :=
    not_locked_ghost γ th q ** globals q.
  #[global] Arguments not_locked /.
  #[global] Arguments globals /.

  #[global] Instance not_locked_timeless `{Σ : cpp_logic, !G Σ} {σ : genv}
      this γ th q : Timeless (not_locked this γ th q).
  Proof. rewrite /not_locked /not_locked_ghost /globals. apply _. Qed.
  #[global] Instance not_locked_exclusive `{Σ : cpp_logic, !G Σ} {σ : genv}
      this γ th : Exclusive1 (not_locked this γ th).
  Proof.
    intros q1 q2. rewrite /not_locked /not_locked_ghost.
    iIntros "[[F1 _] _] [[F2 _] _]".
    iDestruct (Sets0.mutex_set_frag_exclusive with "[$F1 $F2]") as %[].
  Qed.

  (** Public ownership includes the physical owner written by [lock]. *)
  Definition locked `{Σ : cpp_logic, !G Σ} {σ : genv}
      (this : ptr) (γ : gname) (th : thread_idT) (q : cQp.t) : mpred :=
    globals q **
      (this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m (Some th) **
        owner_token γ th q).
  #[global] Arguments locked /.
  #[global] Instance locked_timeless `{Σ : cpp_logic, !G Σ} {σ : genv}
      this γ th q : Timeless (locked this γ th q).
  Proof. rewrite /locked /globals. apply _. Qed.
  #[global] Instance locked_exclusive `{Σ : cpp_logic, !G Σ} {σ : genv}
      this γ : Exclusive2 (locked this γ).
  Proof.
    intros th1 th2 q1 q2. rewrite /locked.
    apply observe_2_sep_r. apply observe_2_sep_r. apply _.
  Qed.

End CustomMutexState.

Module LockState := CustomMutexState MutexSets MutexTokens OwnerTid.

(** Verify the implementation using its ghost resources and public state predicates. *)
Module custom_mutex.
  Module State := LockState.
  Module Spec := mutex_spec State.

  Abbreviation N := "MyMutex"%cpp_name.
  Abbreviation thread_idR := LockState.thread_idR.
  #[local] Hint Opaque LockState.thread_idR : sl_opacity typeclass_instances.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
    WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.

  (* thread::id operations and yield() are not proved for now. *)
  Section unproved_specs.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ}.
    Context `{MOD : source ⊧ σ}.

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

    cpp.spec "std::this_thread::yield()" as yield_spec with (
      \post emp).
  End unproved_specs.

  Definition gname : Set := State.mutex_gname.
  Definition lock_state_gname (γ : gname) : State.gname := γ.
  Definition cinv_gname : gname -> iprop.gname := State.invariant_gname.

  Definition lock_namespace : namespace := nroot .@@ "MyMutex".

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ,
      !State.G Σ}.

    (** The physical lock bit agrees with the abstract ghost state. The
        protected resources and cleared owner field are available while free. *)
    Definition mutex_inv (this : ptr) (γ : gname) (P : mpred) : mpred :=
      ∃ b : bool,
      this ,, _field "MyMutex::m_lock" |->
        atomic.R "int" 1$m (if b then 1 else 0)%Z **
      State.state γ b **
      if b then emp else
        P ** this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None.

    Definition IR (γ : gname) (q : cQp.t) (P : mpred) : Rep :=
      structR N q$m **
      as_Rep (fun this =>
        cinv lock_namespace (cinv_gname γ) (mutex_inv this γ P) **
        cinv_own (cinv_gname γ) q
      ).
    Hint Opaque IR : sl_opacity typeclass_instances.
    #[only(type_ptr,cfractional,ascfractional,cfracvalid)] derive IR.

    Context `{MOD : source ⊧ σ}.

    cpp.spec "MyMutex::MyMutex()" as ctor_spec with
      (\exact Reduce (Spec.ctor_spec IR lock_state_gname)).

    cpp.spec "MyMutex::~MyMutex()" as dtor_spec with
      (\exact Reduce (Spec.dtor_spec IR lock_state_gname)).

    Definition T : Type := gname * mpred.
    cpp.spec "MyMutex::do_lock()" as do_lock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre{(qt : cQp.t)} State.not_locked_ghost g thr qt ** State.globals qt
      \post P ** State.globals qt **
        this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None **
        State.owner_token g thr qt).

    cpp.spec "MyMutex::do_unlock()" as do_unlock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre{qt} State.globals qt **
        this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None **
        State.owner_token g thr qt
      \pre ▷P
      \post State.not_locked_ghost g thr qt ** State.globals qt).

    Definition do_lock := Spec.do_lock lock_state_gname.
    #[global] Arguments do_lock /.
    Definition do_unlock := Spec.do_unlock lock_state_gname.
    #[global] Arguments do_unlock /.

    #[global] Instance custom_mutex_basic_lockable :
        BasicLockable (T := T) (Tnamed N)
          (fun q gP => IR gP.1 q gP.2) :=
      { do_lock := do_lock
      ; do_unlock := do_unlock }.

    cpp.spec "MyMutex::lock()" as lock_spec_alt with
      (\exact Reduce (Spec.lock_spec_alt IR lock_state_gname)).

    cpp.spec "MyMutex::unlock()" as unlock_spec_alt with
      (\exact Reduce (Spec.unlock_spec_alt IR lock_state_gname)).

    cpp.spec "MyMutex::lock()" as lock_spec with
      (\exact Reduce
        (lock_basic_lockable (Tnamed N) (fun q gP => IR gP.1 q gP.2))).

    cpp.spec "MyMutex::unlock()" as unlock_spec with
      (\exact Reduce
        (unlock_basic_lockable (Tnamed N) (fun q gP => IR gP.1 q gP.2))).

    Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

    Definition bi_later_exist_F := [FWD] @bi.later_exist.
    Definition bi_later_sep_F := [FWD] @bi.later_sep.
    Hint Resolve bi_later_exist_F bi_later_sep_F : br_hints.

    #[program]
    Definition do_exchange_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming{qt} State.not_locked_ghost g thr qt
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p,, o_field σ "MyMutex::m_lock") ) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 0 \/ res = 1 |]%Z **
                          if bool_decide (res = 0) then P ** State.owner_token g thr qt **
                            p ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
                          else State.not_locked_ghost g thr qt)
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
      iDestruct "Inv" as (b) "(>L & State & Resources)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if b then 1 else 0)%Z.
      iSplitL "L".
      { ework $usenamed=true with br_erefl. }
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L State Resources]") as "_".
        { iNext. rewrite /mutex_inv. iExists b.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros "L". iMod "Y" as "_".
        destruct b.
        + iMod ("Hclose" with "[L State Resources]") as "_".
          { iNext. rewrite /mutex_inv. iExists true.
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iFrame. }
          iModIntro. rewrite /IR _at_sep _at_as_Rep /=.
          iFrame "CI". iFrame. iPureIntro. auto.
        + iDestruct "Resources" as "[P Owner]".
          iMod (State.do_lock with "[$State $NL]") as "[State Locked]".
          iMod ("Hclose" with "[L State]") as "_".
          { iNext. rewrite /mutex_inv. iExists true.
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iFrame. }
          iModIntro. rewrite /IR _at_sep _at_as_Rep /=.
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
      \consuming{qt} State.owner_token g thr qt
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store "int" (BASE (p ,, o_field σ "MyMutex::m_lock")) 0%Z K
      \instantiate K := (p |-> IR g q P ** State.not_locked_ghost g thr qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & P & Owner & Locked)".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc /=.
      iInv lock_namespace as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (b) "(>L & State & Resources)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if b then 1 else 0)%Z.
      iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      destruct b.
      - iMod (State.do_unlock with "[$State $Locked]") as "[State NL]".
        iMod ("Hclose" with "[L State P Owner]") as "_".
        { iNext. rewrite /mutex_inv. iExists false.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro.
        rewrite /IR _at_sep _at_as_Rep /=.
        iFrame "CI". iFrame.
      - iDestruct (State.unlocked_owner_token with "[$State $Locked]") as %[].
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
      Unshelve. all: exact (1$m)%cQp.
    Qed.

    Lemma mymutex_unlock_alt_proof : verify[source] unlock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec.
      repeat (go; ework).
      Unshelve. all: exact (1$m)%cQp.
    Qed.

    Lemma mymutex_ctor_proof : verify[source] "MyMutex::MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wname [structR] "S".
      wname [P] "P".
      wname [_ |-> atomic.R _ _ _] "L".
      wname [_ |-> thread_idR _ _] "Owner".
      iMod (cinv_alloc_cofinite ∅ ⊤ lock_namespace) as (gi) "(_ & CO & Halloc)".
      iMod (State.alloc γpool gi) as (gs) "(%Hpool & %Hinv & T & State)".
      iMod ("Halloc" $! (mutex_inv this gs P)
        with "[] [L P Owner State]") as "#CI".
      { iPureIntro. rewrite /mutex_inv. apply _. }
      { iNext. rewrite /mutex_inv /=. iExists false. iFrame. }
      iModIntro. iExists gs.
      iSplit; first done.
      subst gi.
      rewrite /IR _at_sep _at_as_Rep /cinv_gname /=.
      iFrame "CI". iFrame.
    Qed.

    Lemma mymutex_dtor_proof : verify[source] "MyMutex::~MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite /IR /mutex_inv.
      work.
      wname [cinv] "#CI".
      wname [cinv_own] "CO".
      wname [State.token] "T".
      iMod (cinv_cancel with "CI CO")
        as "Inv"; [done..|].
      go.
      iDestruct "Inv" as (b) "(Lock & State & Resources)".
      destruct b.
      - iDestruct (State.locked_full_token with "[$State $T]") as %[].
      - iDestruct "Resources" as "[P Owner]".
        iAssert emp with "[State T]" as "_".
        { iApply (affine with "[State T]"); last iAccu. apply mpred_BiAffine. }
        ego $usenamed=true with br_erefl.
    Qed.

    Lemma mymutex_lock_proof : verify[source] lock_spec.
    Proof using MOD HAS_THREADS.
      have -> : lock_spec ⊣⊢ lock_spec_alt.
      { apply (Spec.lock_spec_equiv_lock_spec_alt IR lock_state_gname). done. }
      exact mymutex_lock_alt_proof.
    Qed.

    Lemma mymutex_unlock_proof : verify[source] unlock_spec.
    Proof using MOD HAS_THREADS.
      have -> : unlock_spec ⊣⊢ unlock_spec_alt.
      { apply (Spec.unlock_spec_equiv_unlock_spec_alt IR lock_state_gname). done. }
      exact mymutex_unlock_alt_proof.
    Qed.

  End with_Σ.
End custom_mutex.
