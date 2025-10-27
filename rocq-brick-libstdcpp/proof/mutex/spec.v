Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.inc_hpp.
Require Export bluerock.brick.libstdcpp.runtime.pred.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter mutex_rep : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive mutex_rep.
  (*
  #[global] Declare Instance mutex_rep_typed : Typed3 "std::mutex" mutex_rep.
  #[global] Declare Instance mutex_rep_cfrac : forall γ, CFractional1 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_ascfrac : forall γ, AsCFractional2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_cfracvalid : forall γ, CFracValid2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_timeless : Timeless3 mutex_rep.
  *)
  #[global] Declare Instance mutex_rep_typed : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, Typed3 "std::mutex" mutex_rep.

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
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) mutex_rep).


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
      \with R
      \pre ▷R
      \post Exists g, this |-> mutex_rep g 1$m R ** mutex_token g 1$m).

  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep g q R (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_token g q
      \post R ** mutex_locked g thr).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep g q R (* part of both pre and post *)
      \prepost{i} current_thread i
      \pre mutex_token g q
      \post{b}[Vbool b] if b then R ** mutex_locked g i else mutex_token g q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep g q R (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_locked g thr
      \pre ▷R
      \post mutex_token g q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \pre{g R} this |-> mutex_rep g 1$m R ** mutex_token g 1$m
      \post R).

End with_cpp.
