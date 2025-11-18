Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.inc_hpp.
Require Export bluerock.brick.libstdcpp.runtime.pred.

Module mutex.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive R.
  (*
  #[global] Declare Instance mutex_rep_typed : Typed3 "std::mutex" mutex_rep.
  #[global] Declare Instance mutex_rep_cfrac : forall γ, CFractional1 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_ascfrac : forall γ, AsCFractional2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_cfracvalid : forall γ, CFracValid2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_timeless : Timeless3 mutex_rep.
  *)
  #[global] Declare Instance mutex_rep_typed : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, Typed3 "std::mutex" R.

  (* TODO: index this by the specific mutex! Either via a mutex_gname or by making this a Rep *)
  (* TODO: why is this separate from [mutex_rep] *)
  Parameter mutex_token : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive mutex_token.
  (*
  #[global] Declare Instance mutex_token_cfrac : CFractional1 mutex_token.
  #[global] Declare Instance mutex_token_ascfrac : AsCFractional1 mutex_token.
  #[global] Declare Instance mutex_token_cfracvalid : CFracValid1 mutex_token.
  #[global] Declare Instance mutex_token_timeless : Timeless2 mutex_token.
  *)
  #[global] Declare Instance mutex_rep_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).


  (** A resource enforcing that the thread calling unlock must be the same thread
      that owns the lock

  TODO: maybe a bigger test demonstrating the enforcement?
  minimal version: this fails (fill in the obvious stuff)

    \persist{i} >={ L_TI } i
    \pre{j} mutex_locked g j
    test_unlock(std::mutex & m) {
      m.unlock();
    }

    this succeeds:

    \persist{i} >={ L_TI } i
    \pre mutex_locked g i
    same test_unlock
   *)
  Parameter mutex_locked : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> thread_idT -> mpred.
  #[only(timeless,exclusive)] derive mutex_locked.
  (*
  Declare Instance mutex_locked_timeless : Timeless2 mutex_locked.
  Declare Instance mutex_locked_excl g : Exclusive1 (mutex_locked g).
  *)

  Context `{MOD : inc_hpp.source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\this this
      \pre{P} ▷P
      \post Exists g, this |-> R g 1$m P ** mutex_token g 1$m).

  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_token g q
      \post P ** mutex_locked g thr).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \prepost{i} current_thread i
      \pre mutex_token g q
      \post{b}[Vbool b] if b then P ** mutex_locked g i else mutex_token g q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_locked g thr
      \pre ▷P
      \post mutex_token g q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \pre{g P} this |-> R g 1$m P ** mutex_token g 1$m
      \post P).

End with_cpp.
End mutex.

Module recursive_mutex.
Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  (* NOTE: Invariant used to protect resource [r]
    inv (r \\// exists th n, locked th (S n)) *)

  (* recursive mutex -- ownership of the class. *)
  Parameter R : gname -> cQp.t -> Rep.
  #[only(cfractional,ascfractional,timeless,type_ptr="std::recursive_mutex")] derive R.
  #[global] Instance R_learn : Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) R).
  Proof. solve_learnable. Qed.

  (* #[only(cfractional,timeless)] derive mutex_rep. *)
  (** <<token γ q>> if <<q = 1>>, then the mutex is not locked and therefore can be destroyed.
      <<token γ 1>> is shared among threads who has access to the lock, and a call to lock
      turns some of <<token γ q>> into <<given_token γ q>>, unlock does the opposite.
  *)

  Parameter token : gname -> cQp.t -> mpred.
  #[only(cfracsplittable,timeless)] derive token.
  Parameter given_token : gname -> cQp.t -> mpred.
  #[only(timeless)] derive given_token.
  (* #[only(cfracsplittable,timeless)] derive given_token. *)

  (* the mask of recursive_mutex *)
  Definition mask := nroot .@ "std" .@ "recursive_mutex".

  (** <<locked γ th n>> <<th>> owns the mutex <<γ>> <<n>> times. *)
  Parameter locked : gname -> thread_idT -> nat -> mpred.
  Declare Instance mutex_locked_timeless : Timeless3 locked.
  Axiom locked_excl_same_thread : forall g th n m,
    locked g th n ** locked g th m |-- False.
  Axiom locked_excl_different_thread : forall g th th' n m,
    locked g th n ** locked g th' m |-- [| n = 0 \/ m = 0 |] ** True.

  #[global] Declare Instance threadT_eq_decision : EqDecision thread_idT.
  #[global] Declare Instance threadT_countable : Countable thread_idT.

  Parameter used_threads : gname -> gset thread_idT -> mpred.
  Axiom use_thread : forall th g m,
    th ∉ m ->
    current_thread th ** used_threads g m |-- |==> used_threads g (m ∪ {[ th ]}) ** locked g th 0.

  cpp.spec "std::recursive_mutex::recursive_mutex()" as ctor_spec with
    (\this this
     \post Exists g, this |-> R g 1$m ** token g 1 ** used_threads g empty).

  cpp.spec "std::recursive_mutex::~recursive_mutex()" as dtor_spec with
    (\this this
     \pre{g} this |-> R g 1$m
     \pre token g 1
     \pre{ths} used_threads g ths
     \post emp).

  cpp.spec "std::recursive_mutex::lock()" as lock_spec with
    (\this this
      \prepost{q g} this |-> R g q (* part of both pre and post *)
      \persist{i} current_thread i
      \pre{q'} token g q'
      \pre{Q} AC << ∀ n , locked g i n >> @ top \ ↑ mask , empty
                  << locked g i (S n) , COMM Q >>
      \post Q ** given_token g q').

  cpp.spec "std::recursive_mutex::unlock()" as unlock_spec with
    (\this this
      \prepost{q g} this |-> R g q (* part of both pre and post *)
      \persist{i} current_thread i
      \pre{q'} given_token g q'
      \pre{Q} AC << ∀ n , locked g i (S n) >> @ top \ ↑ mask , empty
                  << locked g i n , COMM Q >>
      \post token g q' ** Q).


  (* Alternative style:
      R γ q r ** locked γ th (S n) |--| R γ q r ** r ** was_locked γ th (S n)

      possible solution: two specs/choice in the spec for unlock: either
      {locked γ th (n+1)} unlock() {locked γ th n}
      or
      {was_locked γ th (n+2)} unlock() {locked γ th (n+1)}
   *)

  (* how to wrap this up into an invariant abstraction *)
  Parameter rmutex_namespace : namespace.
  Context `{HasOwn mpredI (excl_authR natO)}.
  Definition inv_rmutex  (g : gname) (P : mpred) : mpred :=
    inv rmutex_namespace
      (Exists n, own g (●E n) **
        ([|n = 0|] ** P ** own g (◯E n) \\// [|n > 0|] ** Exists th, locked g th n)).

  (** [acquire_state] tracks the acquisition state of a recursive_mutex.
   *)
  Inductive acquire_state {TT : tele} : Type :=
  | NotHeld                (* not held *)
  | Held (n : nat) (xs : TT) (* acquired [n + 1] times with quantifiers [xs] *).
  #[global] Arguments acquire_state _ : clear implicits.

  Definition acquire {TT} (a a' : acquire_state TT) : Prop :=
    match a with
    | NotHeld => exists xs, a' = Held 0 xs
    | Held n xs => a' = Held (S n) xs
    end.
  Definition release {TT} (a : acquire_state TT) : acquire_state TT :=
    match a with
    | NotHeld => NotHeld (* unreachable *)
    | Held n xs =>
        match n with
        | 0 => NotHeld
        | S n => Held n xs
        end
    end.

  Definition acquireable (g : gname) (th : thread_idT) {TT: tele} (t : acquire_state TT) (P : TT -t> mpred) : mpred :=
    match t with
    | NotHeld => locked g th 0
    | Held n args => own g (◯E (S n)) ** tele_app P args
    end.

  #[global] Instance acquireable_learn γ th TT : LearnEq2 (@acquireable γ th TT).
  Proof. solve_learnable. Qed.

  (* TODO make this into a hint *)
  Lemma is_held {TT : tele} {t1 t2: acquire_state TT} :
    acquire t1 t2 ->
    ∃ n xs, t2 = Held n xs /\
      t1 = release t2.
  Proof.
    intros.
    destruct t1; simpl in H; eauto.
    - exists 0. naive_solver.
    - exists (S n). naive_solver.
  Qed.

  #[program]
  Definition acquireable_is_acquired_C {TT : tele} g th t t' P
      (_ : acquire (TT:=TT) t t') :=
    \cancelx
    \consuming acquireable g th t' P
    \deduce{n args} tele_app P args
    \deduce [| t' = Held n args /\ t = release t' |]
    \deduce own g (◯E (S n))
    \end.
  Next Obligation.
    (* TODO use is_held *)
    intros.
    rewrite /acquireable.
    apply is_held in a as (? & ? & -> & ->).
    go. iExists _, _. go.
  Qed.

  #[program]
  Definition own_P_is_acquireable_C {TT : tele} g n P args :=
    \cancelx
    \consuming tele_app P args
    \consuming own g (◯E (S n))
    \proving{th} acquireable(TT:=TT) g th (Held n args) P
    \end.
  Next Obligation. rewrite /acquireable; work. Qed.

  Definition update {TT : tele} (f : TT -t> TT)
    (x : acquire_state TT)
    : acquire_state TT :=
    match x with
    | NotHeld => NotHeld
    | Held n xs => Held n (tele_app f xs)
    end.

  (* TODO maybe a hint that says
    TCEq f1 f2 ->
    acquireable _ _ f1 ⊢ acquireable _ _ f2.
    *)
  Lemma update_eq {TT : tele} f t1 t2 : acquire t1 t2 ->
      update f t1 = release(TT:=TT) (update f t2).
  Proof.
    by intros ([|] & ? & -> & ->)%is_held.
  Qed.

  (* this is the usable pre-condition *)
  #[ignore_missing]
  cpp.spec "rmutex_client(std::recursive_mutex&)" with
    (\arg{mut} "mut" (Vref mut)
     \persist{g tt P} inv_rmutex g (∃ xs : tele_arg tt, tele_app P xs)
     \prepost{q} mut |-> R g q
     \prepost{th n} acquireable g th n P
     \post emp).

  cpp.spec "std::recursive_mutex::lock()" as lock_spec' with
    (\this this
     \persist{g tt P} inv_rmutex g (∃ xs : tele_arg tt, tele_app P xs)
     \prepost{q} this |-> R g q
     \pre{th n} acquireable g th n P
     \pre{q'} token g q'
     \post given_token g q' ** Exists n', [| acquire n n' |] ** acquireable g th n' P).
  (* to prove: this is derivable from lock_spec *)

  cpp.spec "std::recursive_mutex::unlock()" as unlock_spec' with
    (\this this
     \persist{g tt P} inv_rmutex g (∃ xs : tele_arg tt, tele_app P xs)
     \prepost{q} this |-> R g q
     \pre{th n args} acquireable g th (Held n args) P
     \pre{q'} given_token g q'
     \post token g q' ** acquireable g th (release $ Held n args) P).

  Lemma lock_spec_impl_lock_spec' :
    lock_spec |-- lock_spec'.
  Proof.
    apply specify_mono_fupd; work.
    iExists q.
    iModIntro; work.
    iExists q'.
    work.
    iExists (∃ t : acquire_state tt, [| acquire n t |] ∗
              acquireable g th t P)%I.
    work.
    wname [bi_wand] "W".
    iSplitR "W".
    - iAcIntro; rewrite /commit_acc/=.
      wname [inv_rmutex] "I".
      iInv "I" as (?) "?" "Hclose"; [admit|].
      iApply fupd_mask_intro; [set_solver|].
      work.
  Admitted.

  Opaque release.
  Opaque acquireable.

End with_cpp.

#[global] Hint Resolve acquireable_is_acquired_C : br_hints.
#[global] Hint Resolve own_P_is_acquireable_C : br_hints.

End recursive_mutex.
