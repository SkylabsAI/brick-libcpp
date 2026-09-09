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

(** A MUTEX_PREDS says a mutex spec is parametrized by some `token`, `not_locked`
  and `locked`. The exact model depends on the implementation. *)
Module Type MUTEX_PREDS.
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
End MUTEX_PREDS.

(* TODO UPSTREAM. *)
#[global] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

Module mutex_spec (Preds : MUTEX_PREDS).
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} {Name : Type}.
  Context `{!Preds.G Σ}.
  Context (R : Name -> cQp.t -> mpred -> Rep).
  Context (state_name : Name -> Preds.gname).
  Context {HAS_THREADS : HasStdThreads Σ}.

  (** The guarded predicate must be weakly objective for invariant allocation,
      which R likely has. *)
  Definition ctor_spec : ptr -> WpSpec mpred val val :=
    (\this this
      \pre{P γpool} ▷P ** [| WeaklyObjective P |]
      \post |={⊤}=> Exists g, [| Preds.pool_name (state_name g) = γpool |] **
              this |-> R g 1$m P ** Preds.token (state_name g) 1).

  Definition dtor_spec : ptr -> WpSpec mpred val val :=
    (\this this
      \pre{g P} this |-> R g 1$m P ** Preds.token (state_name g) 1
      \post P).

  Definition lock_spec_alt : ptr -> WpSpec mpred val val :=
    (\this this
      \prepost{q P g} this |-> R g q P
      \persist{thr} current_thread thr
      \pre{qt} Preds.not_locked this (state_name g) thr qt
      \post P ** Preds.locked this (state_name g) thr qt).

  Definition unlock_spec_alt : ptr -> WpSpec mpred val val :=
    (\this this
      \prepost{q P g} this |-> R g q P
      \persist{thr} current_thread thr
      \pre{qt} Preds.locked this (state_name g) thr qt
      \pre ▷P
      \post Preds.not_locked this (state_name g) thr qt).

  Definition try_lock_spec_alt : ptr -> WpSpec mpred val val :=
    (\this this
      \prepost{q P g} this |-> R g q P
      \persist{thr} current_thread thr
      \pre{qt} Preds.not_locked this (state_name g) thr qt
      \post{b}[Vbool b]
        if b then P ** Preds.locked this (state_name g) thr qt
        else Preds.not_locked this (state_name g) thr qt).

  (* TODO readd the later on the lock/unlock continuations. *)
  Definition do_lock (this : ptr) (lk : Name * mpred) (K : mpred) : mpred :=
    ∃ thr qt, current_thread thr ** Preds.not_locked this (state_name lk.1) thr qt **
      (Preds.locked this (state_name lk.1) thr qt ** lk.2 -* K).
  #[global] Arguments do_lock /.

  Definition do_unlock (this : ptr) (lk : Name * mpred) (K : mpred) : mpred :=
    ∃ thr qt, current_thread thr ** Preds.locked this (state_name lk.1) thr qt ** ▷lk.2 **
      (Preds.not_locked this (state_name lk.1) thr qt -* K).
  #[global] Arguments do_unlock /.

  Definition do_try_lock (this : ptr) (lk : Name * mpred)
      (K : bool -> mpred) : mpred :=
    ∃ thr qt, current_thread thr ** Preds.not_locked this (state_name lk.1) thr qt **
      ∀ b : bool,
        (if b then lk.2 ** Preds.locked this (state_name lk.1) thr qt
          else Preds.not_locked this (state_name lk.1) thr qt) -* K b.
  #[global] Arguments do_try_lock /.

  Section equivalences.
    Context (method_name class_name : globname).
    Context {BL : BasicLockable (Tnamed class_name) (fun q gp => R gp.1 q gp.2)}.

    Definition spec_type_void_to_ret := (fun ret => specify {| info_name := method_name; info_type := tMethod class_name QM ret [] |}).
    
    Local Lemma method_spec_equiv (ret : type)
        (Pspec Qspec : ptr -> WpSpec mpred val val)
        (Heq : forall this xs K, Pspec this xs K ⊣⊢ Qspec this xs K) :
      spec_type_void_to_ret ret Pspec ⊣⊢ spec_type_void_to_ret ret Qspec.
    Proof.
      iSplit; iApply specify_mono; intros this xs K; rewrite Heq; done.
    Qed.

    Lemma lock_spec_entails_lock_spec_alt
        (Hlock : requirements.do_lock (Tnamed class_name) = do_lock) :
      spec_type_void_to_ret "void"
        (lock_basic_lockable (Tnamed class_name) (fun q gp => R gp.1 q gp.2)) ⊣⊢
      spec_type_void_to_ret "void" lock_spec_alt.
    Proof.
      apply method_spec_equiv. intros this xs K.
      unfold lock_basic_lockable. rewrite Hlock.
      unfold lock_spec_alt, do_lock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HNL & HK)".
        iExists q, (g, P), (P ** Preds.locked this (state_name g) thr qt)%I.
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HNL".
        iIntros "[HL HP]". iFrame.
    Qed.

    Lemma unlock_spec_entails_unlock_spec_alt
        (Hunlock : requirements.do_unlock (Tnamed class_name) = do_unlock) :
      spec_type_void_to_ret "void" (unlock_basic_lockable (Tnamed class_name) (fun q gp => R gp.1 q gp.2)) ⊣⊢
      spec_type_void_to_ret "void" unlock_spec_alt.
    Proof.
      apply method_spec_equiv. intros this xs K.
      unfold unlock_basic_lockable. rewrite Hunlock.
      unfold unlock_spec_alt, do_unlock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HL & HP & HK)".
        iExists q, (g, P), (Preds.not_locked this (state_name g) thr qt).
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HL HP".
        iIntros "$".
    Qed.

    Context {L : Lockable (Tnamed class_name) (fun q gp => R gp.1 q gp.2)}.

    Lemma try_lock_spec_entails_try_lock_spec_alt
        (Htry_lock : requirements.do_try_lock (Tnamed class_name) = do_try_lock) :
      spec_type_void_to_ret "bool" (try_lock_lockable (Tnamed class_name) (fun q gp => R gp.1 q gp.2)) ⊣⊢
      spec_type_void_to_ret "bool" try_lock_spec_alt.
    Proof.
      apply method_spec_equiv. intros this xs K.
      unfold try_lock_lockable. rewrite Htry_lock.
      unfold try_lock_spec_alt, do_try_lock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HNL & HK)".
        iExists q, (g, P), (fun b : bool =>
          if b then (P ** Preds.locked this (state_name g) thr qt)%I
          else Preds.not_locked this (state_name g) thr qt).
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HNL".
        iIntros (b) "$".
    Qed.
  End equivalences.
End with_cpp.
End mutex_spec.


(** Specialize the reusable specs to the standard mutex representation and
    bind them to their C++ names. *)
Module StdMutex (Preds : MUTEX_PREDS).
  Module Spec := mutex_spec Preds.

  Definition gname := Preds.gname.
  Definition lock_state_gname (g : gname) := g.
  Abbreviation cinv_gname := Preds.inv_name.

  Definition G := @Preds.G.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance state_G `{Σ : cpp_logic} (H : G Σ) : Preds.G Σ := H.

  Abbreviation token := Preds.token.
  Abbreviation not_locked := Preds.not_locked.
  Abbreviation locked := Preds.locked.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
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
      Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> req_eq ==> learn_hints.fin) locked).
  Proof. solve_learnable. Qed.

  cpp.spec "std::mutex::mutex()" as ctor_spec with
    (\exact Reduce (Spec.ctor_spec R lock_state_gname)).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
    (\exact Reduce (Spec.dtor_spec R lock_state_gname)).

  cpp.spec "std::mutex::lock()" as lock_spec_alt with
    (\exact Reduce (Spec.lock_spec_alt R lock_state_gname)).

  cpp.spec "std::mutex::unlock()" as unlock_spec_alt with
    (\exact Reduce (Spec.unlock_spec_alt R lock_state_gname)).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec_alt with
    (\exact Reduce (Spec.try_lock_spec_alt R lock_state_gname)).

  Definition do_lock := Spec.do_lock lock_state_gname.
  #[global] Arguments do_lock /.
  Definition do_unlock := Spec.do_unlock lock_state_gname.
  #[global] Arguments do_unlock /.
  Definition do_try_lock := Spec.do_try_lock lock_state_gname.
  #[global] Arguments do_try_lock /.

  (** <<std::mutex>> implements [BasicLockable] and [Lockable]. *)
  Definition T : Type := gname * mpred.

  #[global] Instance mutex_basic_lockable :
      BasicLockable (T:=T) "std::mutex" (λ q γP, R γP.1 q γP.2) :=
    { do_lock := do_lock
    ; do_unlock := do_unlock }.

  cpp.spec "std::mutex::lock()" as lock_spec with
    (\exact Reduce (lock_basic_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
    (\exact Reduce (unlock_basic_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  #[global] Instance mutex_lockable :
      Lockable (T:=T) "std::mutex" (λ q γP, R γP.1 q γP.2) :=
    { do_try_lock := do_try_lock }.

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
    (\exact Reduce (try_lock_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  Lemma lock_spec_entails_lock_spec_alt : lock_spec -|- lock_spec_alt.
  Proof.
    apply (Spec.lock_spec_entails_lock_spec_alt R lock_state_gname).
    reflexivity.
  Qed.

  Lemma unlock_spec_entails_unlock_spec_alt : unlock_spec -|- unlock_spec_alt.
  Proof.
    apply (Spec.unlock_spec_entails_unlock_spec_alt R lock_state_gname).
    reflexivity.
  Qed.

  Lemma try_lock_spec_entails_try_lock_spec_alt : try_lock_spec -|- try_lock_spec_alt.
  Proof.
    apply (Spec.try_lock_spec_entails_try_lock_spec_alt R lock_state_gname).
    reflexivity.
  Qed.
End with_cpp.
End StdMutex.

(** The standard-library implementation remains abstract; concrete mutex
    implementations instantiate [MUTEX_PREDS] beside their proofs. *)
Declare Module StdMutexState : MUTEX_PREDS with Definition Q := Qp.
Module StdMutexInst := StdMutex StdMutexState.
Module mutex := StdMutexInst.
