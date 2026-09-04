Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.lock_guard.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!mutex.G Σ}.

  Import lock_guard.

  (* TODO: not ideal *)
  #[global] Instance UNSAFE_R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> learn_eq ==> learn_eq ==> fin_at) mutex.R).
  Proof. solve_learnable. Qed.

  #[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.

  Lemma ctor_ok : verify[source] ctor_spec.
  Proof.
    verify_spec.
    go.
    iExists (mutex.locked g (Some thr) qt ** P), qt.
    go with br_erefl.
    by rewrite (left_id_L 1%Qp Qp.mul).
  Qed.

  Lemma dtor_ok : verify[source] dtor_spec.
  Proof.
    verify_spec.
    rewrite !R.unlock.
    go.
    iExists (mutex.not_locked g thr qt), qt.
    go with br_erefl.
    by rewrite (left_id_L 1%Qp Qp.mul).
  Qed.

End with_cpp.
