Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.test_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!lockG Σ}.

  cpp.spec "test_mutex()" as test_mutex_spec from source with (
        \post emp).

  (* #[program] *)
  (* Definition login_C E (th : thread_idT) (g : gname) (s : gset thread_idT) := *)
  (*   \cancelx *)
  (*   \masks MatchFUpd E E => NoConfig *)
  (*   \consuming lock_ghost.used_threads g s *)
  (*   \preserving current_thread th *)
  (*   (* \require th ∉ s *) *)
  (*   \using [| th ∉ s |] *)
  (*   \deduce lock_ghost.users g {[th]} *)
  (*   \deduce lock_ghost.used_threads g (s ∪ {[th]}) *)
  (*   \end. *)
  (* Next Obligation. *)
  (*   intros; work. *)
  (*   wapply (lock_ghost.login th g s); first set_solver; work. *)
  (*   iModIntro; work. *)
  (* Qed. *)

  Import wp_notations.Verbose.

  Theorem test_mutex_ok : verify[source] "test_mutex()".
  Proof.
    verify_spec; go.
    iExists emp.
    wuntil Emember_call go.

    ren_hyp g gname.
    wapply current_thread_always_exists; work.
    wapply (lock_ghost.login t g ∅); first set_solver.

    (* Depends on fewer details, but more awkward. *)
    Succeed
      solve [
        wuntil (FreeTemps.delete "std::mutex") go; run1; iApply fupd_wp_destroy_named;
        wapply (lock_ghost.logout t g ∅); first set_solver; work; iModIntro; go].

    (* Easier, but more fragile: [Kfree] might disappear. *)
    wuntil Kfree go.
    wapply (lock_ghost.logout t g ∅); first set_solver.
    go.
  Qed.

  cpp.spec "test_lock_guard()" as test_lock_guard_spec from source with (\post emp).

  Lemma test_lock_guard_ok : verify[source] "test_lock_guard()".
  Proof.
    verify_spec; go.
    iExists emp.
    wuntil Econstructor go.

    ren_hyp g gname.
    wapply current_thread_always_exists; work.
    wapply (lock_ghost.login t g ∅); first set_solver.
    wuntil Kfree go; run1; wuntil Kfree go.

    wapply (lock_ghost.logout t g ∅); first set_solver.

    go.
  Qed.

  cpp.spec "test_scoped_lock()" as test_scoped_lock_spec from source with (\post emp).

  Lemma test_scoped_lock_ok : verify[source] "test_scoped_lock()".
  Proof.
    verify_spec; go.
    iExists emp; go.
    iExists emp.
    wuntil Econstructor go.
    wapply current_thread_always_exists; work.
    wapply (lock_ghost.login t _ ∅); last work with br_erefl; first set_solver.
    wapply (lock_ghost.login t _ ∅); last work with br_erefl; first set_solver.
    wuntil Kfree go. run1.
    wuntil interp go.
    wapply (lock_ghost.logout t _ ∅); first set_solver.
    step with br_erefl.
    wapply (lock_ghost.logout t _ ∅); first set_solver.
    go with br_erefl.
  Qed.

  cpp.spec "test_unique_lock()" as test_unique_lock_spec from source with (\post emp).

  Lemma test_unique_lock_ok : verify[source] "test_unique_lock()".
  Proof.
    verify_spec.
    go.
    iExists emp.
    wuntil Econstructor go.

    ren_hyp g gname.
    wapply current_thread_always_exists; work.
    wapply (lock_ghost.login t g ∅); first set_solver.
    wuntil Kfree go; run1; wuntil Kfree go.
    wapply (lock_ghost.logout t g ∅); first set_solver.
    go.
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
    verify_spec; go. iExists emp.
    wuntil Econstructor go.

    ren_hyp g gname.
    wapply current_thread_always_exists; work.
    wapply (lock_ghost.login t g ∅); first set_solver.

    wuntil Kfree go.
    wapply (lock_ghost.logout t g ∅); first set_solver.
    go.
  Qed.
End with_cpp.
