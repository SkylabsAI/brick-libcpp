Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.mutex.test_cpp.
Require Import bluerock.brick.libstdcpp.mutex.spec.

Section with_cpp.
  Context `{Σ : cpp_logic} {HAS_THREADS : HasStdThreads Σ}.
  Context `{MOD : test_cpp.source ⊧ σ}. (* σ is the whole program *)

  cpp.spec "test()" as test_spec with
      (\post emp).

  Theorem test_ok : verify[source] test_spec.
  Proof using HAS_THREADS.
    verify_spec; go.
    iExists emp; go.
  Qed.

End with_cpp.
