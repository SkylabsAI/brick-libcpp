Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libcpp.semaphore.test_cpp. (* TODO: should be changed to [inc_hpp] *)

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

  (* write this as a logically atomic triple *)
  cpp.spec "std::__1::counting_semaphore<1l>::counting_semaphore(long)" as ctor_spec with
      (\this this
       \arg{desired} "desired" (Vnat desired)
       \post Exists g, this |-> semaphoreR 1$m g ** semaphore_Val g desired).
  (* note that technically mutex needs to know which thread holds it *)

  cpp.spec "std::__1::counting_semaphore<1l>::acquire()" as acquire_spec with
      (\this this
       \prepost{q g} this |-> semaphoreR q g
       \pre{Q} AC << ∀ n, semaphore_Val g n >> @ top, empty
                  << Exists n', [|n = S n'|] ** semaphore_Val g n', COMM Q  >>
       \post Q).

  cpp.spec "std::__1::counting_semaphore<1l>::try_acquire()" as try_lock_spec with
      (\this this
         \prepost{q g} this |-> semaphoreR q g (* part of both pre and post *)
         \pre{Q} AU <{ ∃∃ n, semaphore_Val g n }> @ top, empty
                  <{ semaphore_Val g (if bool_decide (n = 0) then n else n-1), COMM Q $ bool_decide (n = 0) }>
        \post{b}[Vbool b] (Q b)).

  cpp.spec "std::__1::counting_semaphore<1l>::release(long)" as release_spec with
      (\this this
        \arg{update} "update" (Vnat update)
        \prepost{q g} this |-> semaphoreR q g
        \pre{Q} AC << ∀ n, semaphore_Val g n ∗ [| n+update <= 1 |] >> @ top, empty
                   << semaphore_Val g (n+update), COMM Q  >>
       \post Q).

  cpp.spec "std::__1::counting_semaphore<1l>::~counting_semaphore()" as dtor_spec with
      (\this this
        \pre{g} this |-> semaphoreR 1$m g 
        \post emp).

  cpp.spec "test()" as test_spec with
      (\post emp).

  Declare Instance semaphoreR_typed : Typed2 "std::__1::counting_semaphore<1l>" semaphoreR.

  (* LHS learns RHS *)
  #[global] Declare Instance inst v n : Refine1 true true (Vint v = Vnat n) ([n = Z.to_nat v]).
  #[global] Declare Instance semaphoreR_learnable : LearnEqF1 semaphoreR.
  
  #[program]
  Definition ac_C t (x:nat) :=
    \cancelx
    \consuming semaphore_Val t x
    \bound_existential Q
    \proving AC << ∀ n : nat, semaphore_Val t n >> @ ⊤, ∅
         << ∃ n' : nat, [| n = S n' |] ∗
          semaphore_Val t n',
        COMM Q >>
    \instantiate Q:=emp
    \through ([| 0 < x |] ∗ semaphore_Val t (x - 1) -∗ emp)
    \end.
  Next Obligation. Admitted.
  Hint Resolve ac_C : br_opacity.

  Theorem test_ok : verify[module] test_spec.
  Proof. verify_spec; go.
    Fail progress go using ac_C.
  Admitted.


End with_cpp.
