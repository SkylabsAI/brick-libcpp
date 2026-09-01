Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.test_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!lockG Σ}.

  cpp.spec "test_mutex()" as test_mutex_spec from source with (\post emp).

  Theorem test_mutex_ok : verify[source] "test_mutex()".
  Proof.
    verify_spec; go.
    iExists emp. go.
  Qed.

  cpp.spec "test_lock_guard()" as test_lock_guard_spec from source with (\post emp).

  Lemma test_lock_guard_ok : verify[source] "test_lock_guard()".
  Proof.
    verify_spec; go.
    iExists emp; go.
  Qed.

  cpp.spec "test_scoped_lock()" as test_scoped_lock_spec from source with (\post emp).

  Lemma test_scoped_lock_ok : verify[source] "test_scoped_lock()".
  Proof.
    verify_spec; go.
    iExists emp; go.
    iExists emp; go.
  Qed.

  cpp.spec "test_unique_lock()" as test_unique_lock_spec from source with (\post emp).

  Lemma test_unique_lock_ok : verify[source] "test_unique_lock()".
  Proof.
    verify_spec; go.

    iExists emp; go.
  Qed.


  cpp.spec "test_unique_lock_defer()" as test_unique_lock_defer_spec from source with (
    \prepost{q} _global "std::defer_lock" |-> defer_lock_t.R q
    \post emp).

  Lemma test_unique_lock_defer_ok : verify[source] "test_unique_lock_defer()".
  Proof.
    verify_spec; go.
    iExists emp; go.
  Qed.

  cpp.spec "std::move<std::unique_lock<std::mutex>&>(std::unique_lock<std::mutex>&)" from source inline.

  cpp.spec "test_unique_lock_move()" as test_unique_lock_move_spec from source with (
    \post emp).

  Lemma test_unique_lock_move_ok : verify[source] "test_unique_lock_move()".
  Proof.
    verify_spec; go.
    iExists emp; go.
  Qed.
End with_cpp.
