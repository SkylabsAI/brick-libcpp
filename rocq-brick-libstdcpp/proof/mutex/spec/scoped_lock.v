Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

Module scoped_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      cQp.t -> list (ptr * mutex.gname * Qp * Qp * mpred) -> Rep.

    #[only(type_ptr="std::scoped_lock<std::mutex, std::mutex>")] derive R.
    #[only(cfractional,ascfractional,cfracvalid)] derive R.

    Section with_threads.
      Context {σ : genv}.
      Context `{HAS_THREADS : !HasStdThreads Σ}.
      Context `{!mutex.G Σ}.

      #[global] Instance: LearnEqF1 R := ltac:(solve_learnable).

      cpp.spec
      "std::scoped_lock<...<std::mutex, std::mutex>>::scoped_lock(std::mutex&, std::mutex&)"
      (* "std::scoped_lock<std::mutex, std::mutex>::scoped_lock(std::mutex&, std::mutex&)" *)
      as ctor_spec from source with (
        \this this
        \persist{thr} current_thread thr
        \arg{mp1} "" (Vptr mp1)
        \pre{g1 q1 qt1 P1} mp1 |-> mutex.R g1 q1$m P1
        \pre mutex.not_locked g1 thr qt1
        \arg{mp2} "" (Vptr mp2)
        \pre{g2 q2 qt2 P2} mp2 |-> mutex.R g2 q2$m P2
        \pre mutex.not_locked g2 thr qt2
        \post
          this |-> R 1$m [ (mp1, g1, q1, qt1, P1); (mp2, g2, q2, qt2, P2)] **
          P1 ** mutex.locked g1 (Some thr) qt1 **
          P2 ** mutex.locked g2 (Some thr) qt2
      ).

      cpp.spec "std::scoped_lock<...<std::mutex, std::mutex>>::~scoped_lock()"
        as dtor_spec from source with (
        \this this
        \persist{thr} current_thread thr
        \pre{
          mp1 mp2
          g1 q1 qt1 P1
          g2 q2 qt2 P2
        }
          this |-> R 1$m [ (mp1, g1, q1, qt1, P1); (mp2, g2, q2, qt2, P2)]
        \pre |> P1
        \pre |> P2
        \pre mutex.locked g1 (Some thr) qt1
        \pre mutex.locked g2 (Some thr) qt2
        \post
          mp1 |-> mutex.R g1 q1$m P1 ** mutex.not_locked g1 thr qt1 **
          mp2 |-> mutex.R g2 q2$m P2 ** mutex.not_locked g2 thr qt2
      ).
    End with_threads.
  End with_cpp.

End scoped_lock.
