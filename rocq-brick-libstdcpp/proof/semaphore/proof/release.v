Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.semaphore.spec. (* TODO: necessary in order to get the specializations *)

Import auto_frac auto_pick_frac.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context  `{MOD : test_cpp.source ⊧ σ}. (* σ is the whole program *)

  Theorem release_ok : verify?[test_cpp.source] release_spec.
  Proof using MOD.
    verify_spec.
    go.
    (* TODO need to have specs for atomic wait/notify *)
  Admitted.

End with_cpp.
