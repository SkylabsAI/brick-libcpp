Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.prelude.
Require Import skylabs.brick.libstdcpp.mutex.spec.unique_lock.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.lib.tactics.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.

NES.Begin unique_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context `{HAS_THREADS : !HasStdThreads Σ}.
    Context `{!lock_ghost.lockG Σ}.

    Import R_unfold.

    Lemma default_ctor_spec_ok : verify[source] "std::unique_lock<std::mutex>::unique_lock()".
    Proof.
      verify_spec; go.
    Qed.

    cpp.spec "std::__addressof<std::mutex>(std::mutex&)" as __addressof_spec from source with (
      \arg{mp} "" (Vptr mp)
      \post[Vptr mp] emp
    ).

    #[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.

    Lemma lock_defer_ctor_spec_ok :
      __addressof_spec |--
      verify[source]
        "std::unique_lock<std::mutex>::unique_lock(std::mutex&, std::defer_lock_t)".
    Proof.
      verify_spec; go.
      by rewrite cQp.scale_mut (right_id_L 1%Qp Qp.mul).
    Qed.

    #[local] Instance: `{SplitRecord (M T)} := {}.

    Lemma lock_ctor_spec_ok :
      __addressof_spec |--
      verify[source]
        "std::unique_lock<std::mutex>::unique_lock(std::mutex&)".
    Proof.
      verify_spec; go.
      iExists K, q.
      (* Time Succeed solve [setoid_rewrite cQp.scale_mut; setoid_rewrite (right_id_L 1%Qp Qp.mul); ego with br_erefl]. *)

      rewrite cQp.scale_mut (right_id_L 1%Qp Qp.mul).
      go with br_erefl.
    Qed.

  End with_cpp.
NES.End unique_lock.
