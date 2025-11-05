Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.semaphore.spec.
Require Import bluerock.brick.libstdcpp.semaphore.test_cpp.

Import auto_frac auto_pick_frac.

Section with_cpp.
  #[local] Open Scope nat_scope.

  Context `{Σ : cpp_logic}.
  Context  `{MOD : test_cpp.source ⊧ σ}. (* σ is the whole program *)

  #[program]
  Definition ac_C :=
    \cancelx
    \consuming{t (x:nat)} semaphore_Val t x
    \bound_existential Q
    \proving acquire_ac t Q
    \instantiate Q := semaphore_Val t (x - 1) ** [| x > 0 |]
    \end.
  Next Obligation.
    work.
    rewrite /acquire_ac.
    iAcIntro.
    rewrite /commit_acc /=.
    iExists _; iFrame.
    iMod (fupd_mask_subseteq ∅) as "Close"; first by solve_ndisj.
    iIntros "!>" (x)  "[-> ?]".
    iMod "Close". iModIntro.
    replace (S x - 1) with x by lia.
    iFrame. iPureIntro. lia.
  Qed.
  Hint Resolve ac_C : br_hints.

  #[program]
  Definition rel_ac_C :=
    \cancelx
    \consuming{t (x:nat)} semaphore_Val t x
    \bound_existential Q
    \proving{update} release_ac t Q update
    \instantiate Q := semaphore_Val t (x + update)
    \through [| x + update <= 1 |]
    \end.
  Next Obligation.
    work.
    rewrite /release_ac.
    iAcIntro.
    rewrite /commit_acc /=.
    iExists _; iFrame.
    iMod (fupd_mask_subseteq ∅) as "Close"; first by solve_ndisj.
    iFrame "%".
    iIntros "!> $".
    iMod "Close". done.
  Qed.
  Hint Resolve rel_ac_C : br_hints.

  (* TODO try_acquire_ac_C  *)

  cpp.spec "test()" as test_spec with
      (\post emp).

  Theorem test_ok : verify[source] test_spec.
  Proof using MOD.
    verify_spec.
    go.
  Qed.

End with_cpp.
