Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.semaphore.test_cpp. (* TODO: should be changed to [inc_hpp] *)
Set Debug "-backtrace". (* Paolo: Workaround for now-fixed bug.*)

Import auto_frac auto_pick_frac.

Section with_cpp.

  Context `{Σ : cpp_logic}.
  Context  `{MOD : test_cpp.module ⊧ σ}. (* σ is the whole program *)

  Parameter semaphoreR : cQp.t -> gname -> Rep.
  (* #[only(cfractional,timeless)] derive semaphoreR. *)
  Parameter semaphore_Val : gname -> nat -> mpred.

  (*Parameter mutex_token : cQp.t -> mpred.*)


#[global] Declare Instance semaphoreR_cfrac : CFractional1 semaphoreR.
#[global] Declare Instance semaphoreR_ascfrac : AsCFractional1 semaphoreR.
#[global] Declare Instance semaphoreR_cfracvalid : CFracValid1 semaphoreR.
#[global] Declare Instance semaphoreR_timeless : Timeless2 semaphoreR.
#[global] Declare Instance semaphore_Val_affine : Affine2 semaphore_Val.
(* we might now have semaphore implemented with atomics *)

  Definition acquire_ac t Q  : mpred :=
    AC << ∀ n : nat, semaphore_Val t n >> @ ⊤, ∅
       << ∃ n' : nat, [| n = S n' |] ∗ semaphore_Val t n',
        COMM Q >>.
  Hint Opaque acquire_ac : br_opacity.

  (* write this as a logically atomic triple *)
  cpp.spec "std::counting_semaphore<1l>::counting_semaphore(long)" as ctor_spec with
      (\this this
       \arg{desired} "desired" (Vnat desired)
       \post Exists g, this |-> semaphoreR 1$m g ** semaphore_Val g desired).
  (* note that technically mutex needs to know which thread holds it *)

  cpp.spec "std::counting_semaphore<1l>::acquire()" as acquire_spec with
      (\this this
       \prepost{q g} this |-> semaphoreR q g
       \pre{Q} acquire_ac g Q
       \post Q).

  Definition try_acquire_ac g Q : mpred :=
    AU <{ ∃∃ n, semaphore_Val g n }> @ top, empty
       <{ semaphore_Val g (if bool_decide (n = 0) then n else n-1), COMM Q $ bool_decide (n = 0) }>.
  Hint Opaque try_acquire_ac : br_opacity.



  cpp.spec "std::counting_semaphore<1l>::try_acquire()" as try_lock_spec with
      (\this this
         \prepost{q g} this |-> semaphoreR q g (* part of both pre and post *)
         \pre{Q} try_acquire_ac g Q
         (* AU <{ ∃∃ n, semaphore_Val g n }> @ top, empty
                  <{ semaphore_Val g (if bool_decide (n = 0) then n else n-1), COMM Q $ bool_decide (n = 0) }> *)
        \post{b}[Vbool b] (Q b)).

  Definition release_ac g Q update : mpred :=
    AC << ∀ n, semaphore_Val g n ∗ [| n+update <= 1 |] >> @ top, empty
       << semaphore_Val g (n+update), COMM Q  >>.
  Hint Opaque release_ac : br_opacity.

  cpp.spec "std::counting_semaphore<1l>::release(long)" as release_spec with
      (\this this
        \arg{update} "update" (Vnat update)
        \prepost{q g} this |-> semaphoreR q g
        \pre{Q} release_ac g Q update
       \post Q).

  cpp.spec "std::counting_semaphore<1l>::~counting_semaphore()" as dtor_spec with
      (\this this
        \pre{g} this |-> semaphoreR 1$m g
        \post emp).

  cpp.spec "test()" as test_spec with
      (\post emp).


  (* LHS learns RHS *)
  #[global] Declare Instance inst v n : Refine1 true true (Vint v = Vnat n) ([n = Z.to_nat v]).
  #[global] Declare Instance semaphoreR_learnable : LearnEqF1 semaphoreR.

  Theorem release_ok : verify?[module] release_spec.
  Proof using MOD.
    verify_spec.
    go.
    (* TODO need to have specs for atomic wait/notify *)
  Admitted.

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

  Theorem test_ok : verify[module] test_spec.
  Proof using MOD.
    verify_spec.
    go.
  Qed.
    (* Set BR Debug "@all=3".
    progress with_log! go using ac_C. *)


End with_cpp.
