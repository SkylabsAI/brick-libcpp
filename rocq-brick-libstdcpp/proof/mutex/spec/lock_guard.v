Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.


Import linearity.

Section TO_UPSTREAM.
  Lemma cQp_mut_add q1 q2 :
    (q1 + q2)$m%cQp = (q1$m + q2$m)%cQp.
  Proof. done. Qed.
End TO_UPSTREAM.

Module lock_guard.

  sl.lock
  Definition R `{Σ : cpp_logic, !HasStdThreads Σ} {σ : genv} (mp : ptr * gname * Qp) (q : cQp.t) (P : mpred) : Rep :=
    structR "std::lock_guard<std::mutex>" q **
    let '(mp, g, q') := mp in
    _field "std::lock_guard<std::mutex>::_M_device" |-> refR<"std::mutex"> q mp **
    pureR (
      mp |-> mutex.R g (q * q')$m P).

  #[only(type_ptr)] derive R.
  #[only(lazy_unfold)] derive R.

  Section with_RepFor.
    Import rep.RepFor.
    Import RepScheme.

    #[global] Instance repfor `{Σ : cpp_logic, !HasStdThreads Σ} {σ : genv} :
      rep.RepFor.C "std::lock_guard<std::mutex>"
      [ArgType.Constant _; ArgType.CFrac; ArgType.Constant _]
      R := {}.
  End with_RepFor.

  (**
  These automated proofs fail, so we prove it by hand.
  [R_cfrac] does not seem too useful (why ever split a lock guard?), but let's
  prove it anyway to test our infrastructure. *)
  Fail #[only(cfractional,cfracvalid,ascfractional)] derive R.

  #[only(cfracvalid)] derive R.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!lock_ghost.lockG Σ}.

  #[global] Instance R_learn :
    Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) lock_guard.R) :=
    ltac:(solve_learnable).

  Set Printing Coercions.

  Section with_R_cfrac'.
    #[local] Instance R_cfrac' g q' P :
      CFractional (λ q, mutex.R g (cQp.frac q * q')$m P).
    (* Proof.
      intros q1 q2.
      rewrite -(cfractional (P := λ q, mutex.R _ q _)).
      rewrite -cQp_mut_add.
      rewrite -Qp.mul_add_distr_r.
      Succeed done.
      by rewrite -cQp.frac_add.
    Restart.
    *)
    Proof.
      intros q1 q2.
      rewrite cQp.frac_add.
      rewrite Qp.mul_add_distr_r.
      rewrite cQp_mut_add.
      by rewrite (cfractional (P := λ q, mutex.R g q P)).
    Qed.

    #[global] Instance R_cfrac mp : CFractional1 (R mp).
    Proof. rewrite R.unlock. apply _. Qed.
  End with_R_cfrac'.

  Fail #[only(ascfractional)] derive R.
  #[global] Instance R_as_cfrac mp : AsCFractional1 (R mp).
  Proof. solve_as_cfrac. Qed.

  cpp.spec "std::lock_guard<std::mutex>::lock_guard(std::mutex &)" as ctor_spec from source with (
    \this this
    \arg{mp} "m" (Vptr mp)
    \persist{thr} current_thread thr
    \pre{g q P} mp |-> mutex.R g q$m P
    \pre lock_ghost.user g thr
    \post
      this |-> R (mp, g, q) 1$m P **
      P ** mutex.locked g thr
    ).

  cpp.spec "std::lock_guard<std::mutex>::~lock_guard()" as dtor_spec from source with (
    \this this
    \pre{mp g q P} this |-> R (mp, g, q) 1$m P
    \persist{thr} current_thread thr
    \pre mutex.locked g thr
    \pre ▷P
    \post
      lock_ghost.user g thr **
      mp |-> mutex.R g q$m P
  ).

  Section with_prelude.

    Import skylabs.auto.cpp.prelude.proof.

    Lemma mutex_borrow mp g P (this : ptr) (q1 q2 : Qp) :
      this |-> R (mp, g, (q1 + q2)%Qp) 1$m P |--
      mp |-> mutex.R g q1$m P **
      this |-> R (mp, g, q2) 1$m P.
    Proof.
      rewrite R.unlock.
      work.
      iDestruct select (mp |-> mutex.R g _ P) as "[??]".
      (* Unnecessary with our prelude. *)
      (* rewrite !left_id_L. *)
      work.
    Qed.
  End with_prelude.

End with_cpp.
End lock_guard.
