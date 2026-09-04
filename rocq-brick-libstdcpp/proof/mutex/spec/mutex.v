Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.

Import linearity.

(* TODO UPSTREAM. *)
#[global] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

Module Mutex (State : lock_ghost2.MUTEX_STATE).
Include State.

#[global] Hint Opaque token not_locked locked : sl_opacity typeclass_instances.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr="std::mutex")] derive R.
  #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

  Section with_RepFor.
    Import rep.RepFor.
    Import RepScheme.

    #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
      rep.RepFor.C "std::mutex" [ArgType.Constant _; ArgType.CFrac; ArgType.Constant _]
        (funI γ q P => R γ q P) := {}.
  End with_RepFor.


  Context `{!G Σ}.

  Context `{MOD : source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  #[global] Instance locked_learn :
      Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> learn_hints.fin) locked).
  Proof. solve_learnable. Qed.


  cpp.spec "std::mutex::mutex()" as ctor_spec with (
    \this this
    \pre{P} ▷P
    \post Exists g, this |-> R g 1$m P ** token g 1).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with (
    \this this
    \pre{g P} this |-> R g 1$m P ** token g 1
    \post P).

  (* "Inline" version of these specs. *)
  cpp.spec "std::mutex::lock()" as lock_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{thr} current_thread thr
    \pre{qt} not_locked g thr qt
    \post P ** locked g thr qt).

  Definition do_lock (lk : gname * mpred) (K: mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ thr qt, current_thread thr ∗ not_locked g thr qt ∗
    (* TODO readd *)
    (* ▷ *)
    (locked g thr qt ** P -* K).
  #[global] Arguments do_lock /.

  cpp.spec "std::mutex::unlock()" as unlock_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{thr} current_thread thr
    \pre{qt} locked g thr qt
    \pre ▷P
    \post not_locked g thr qt).

  Definition do_unlock (lk : gname * mpred) (Q : mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    Exists thr qt, current_thread thr ** locked g thr qt ** ▷P **
    (* TODO readd *)
    (* ▷ *)
    (not_locked g thr qt -* Q).
  #[global] Arguments do_unlock /.

  cpp.spec "std::mutex::try_lock()" as try_lock_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{th} current_thread th
    \pre{qt} not_locked g th qt
    \post{b}[Vbool b] if b then P ** locked g th qt else not_locked g th qt).

  (* Obtain same specs from (Basic)Lockable. *)
  (** <<std::mutex>> implements [BasicLockable] *)
  Definition T : Type := gname * mpred.

  #[global] Instance mutex_basic_lockable : BasicLockable (T:=T) "std::mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_lock := fun this => do_lock
  ; do_unlock := fun this => do_unlock }.

  cpp.spec "std::mutex::lock()" as lock_spec with
  (\exact Reduce (lock_basic_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
  (\exact Reduce (unlock_basic_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  Definition do_try_lock (lk : gname * mpred) (Q : bool -> mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ thr qt, current_thread thr ∗ not_locked g thr qt ∗
    ∀ b : bool,
    (if b then P ** locked g thr qt else not_locked g thr qt) -∗ Q b.
  #[global] Arguments do_try_lock /.

  #[global,program] Instance mutex_lockable : Lockable (T:=T) "std::mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_try_lock := fun this => do_try_lock }.

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
  (\exact Reduce (try_lock_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  Lemma lock_spec_entails_lock_spec_alt : lock_spec -|- lock_spec_alt.
  Proof.
    iSplit; iApply specify_mono; ework with br_erefl.
  Qed.

  Lemma unlock_spec_entails_unlock_spec_alt : unlock_spec -|- unlock_spec_alt.
  Proof.
    iSplit; iApply specify_mono; ework with br_erefl.
  Qed.

  Lemma try_lock_spec_entails_try_lock_spec_alt : try_lock_spec -|- try_lock_spec_alt.
  Proof.
    iSplit; iApply specify_mono; ework with br_erefl.
  Qed.
End with_cpp.
End Mutex.

(** The standard instantiation.  Clients that need another camera package can
    instantiate [Mutex] with any implementation of [MUTEX_STATE]. *)
Module mutex := Mutex lock_ghost2.LockState.
