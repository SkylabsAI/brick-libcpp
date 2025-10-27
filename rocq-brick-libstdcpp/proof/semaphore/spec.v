Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.semaphore.test_cpp. (* TODO: necessary in order to get the specializations *)

Import auto_frac auto_pick_frac.

(* TODO: upstream *)
#[global] Declare Instance inst v n : Refine1 true true (Vint v = Vnat n) [n = Z.to_nat v].
Section with_cpp.

  Context `{Σ : cpp_logic}.
  Context  `{MOD : test_cpp.source ⊧ σ}. (* σ is the whole program *)

  Parameter semaphoreR : forall {σ : genv}, gname -> cQp.t -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive semaphoreR.
  #[global] Declare Instance semaphoreR_typed : Typed2 "std::counting_semaphore<1l>" semaphoreR.
  #[global] Instance semaphoreR_learnable :
    Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) semaphoreR).
  Proof. solve_learnable. Qed.

  Parameter semaphore_Val : forall {σ : genv}, gname -> nat -> mpred.
  #[global] Declare Instance semaphore_Val_affine : Affine2 semaphore_Val.

  (* we might now have semaphore implemented with atomics *)

  Definition acquire_ac (t : gname) Q  : mpred :=
    AC << ∀ n : nat, semaphore_Val t n >> @ ⊤, ∅
       << ∃ n' : nat, [| n = S n' |] ∗ semaphore_Val t n',
        COMM Q >>.
  Hint Opaque acquire_ac : br_opacity.

  (* write this as a logically atomic triple *)
  cpp.spec "std::counting_semaphore<1l>::counting_semaphore(long)" as ctor_spec with
      (\this this
       \arg{desired} "desired" (Vnat desired)
       \post Exists g, this |-> semaphoreR g 1$m ** semaphore_Val g desired).
  (* note that technically mutex needs to know which thread holds it *)

  cpp.spec "std::counting_semaphore<1l>::acquire()" as acquire_spec with
      (\this this
       \prepost{q g} this |-> semaphoreR g q
       \pre{Q} acquire_ac g Q
       \post Q).

  Definition try_acquire_ac g Q : mpred :=
    AU <{ ∃∃ n, semaphore_Val g n }> @ top, empty
       <{ semaphore_Val g (if bool_decide (n = 0) then n else n-1), COMM Q $ bool_decide (n = 0) }>.
  Hint Opaque try_acquire_ac : br_opacity.

  cpp.spec "std::counting_semaphore<1l>::try_acquire()" as try_lock_spec with
      (\this this
         \prepost{q g} this |-> semaphoreR g q (* part of both pre and post *)
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
        \prepost{q g} this |-> semaphoreR g q
        \pre{Q} release_ac g Q update
       \post Q).

  cpp.spec "std::counting_semaphore<1l>::~counting_semaphore()" as dtor_spec with
      (\this this
       \pre{g} this |-> semaphoreR g 1$m
       \post emp).

End with_cpp.
