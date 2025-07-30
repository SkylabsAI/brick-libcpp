Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libcpp.semaphore.test_cpp. (* TODO: should be changed to [inc_hpp] *)

Section with_cpp.

  Context `{Σ : cpp_logic}.
  Context  `{MOD : test_cpp.module ⊧ σ}. (* σ is the whole program *)

  Parameter semaphoreR : cQp.t -> gname -> Rep.
  #[only(cfractional,timeless)] derive semaphoreR.
  Parameter semaphore_Val : gname -> nat -> mpred.

  (*Parameter mutex_token : cQp.t -> mpred.*)

  (*
#[global] Declare Instance semaphoreR_cfrac : CFractional1 semaphoreR.
#[global] Declare Instance semaphoreR_ascfrac : AsCFractional1 semaphoreR.
#[global] Declare Instance semaphoreR_cfracvalid : CFracValid1 semaphoreR.
#[global] Declare Instance semaphoreR_timeless : Timeless2 semaphoreR.*)

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

  (* up to here*)
(*
  cpp.spec "std::__1::mutex::try_acquire()" as try_lock_spec with
      (\this this
         \prepost{q R} this |-> semaphoreR q R (* part of both pre and post *)
         \pre mutex_token q
         \post{b}[Vbool b] if b then R else mutex_token q).

  cpp.spec "std::__1::mutex::release()" as unlock_spec with
      (\this this
         \prepost{q R} this |-> semaphoreR q R (* part of both pre and post *)
         \pre ▷R
         \post mutex_token q).

  cpp.spec "std::__1::mutex::~mutex()" as dtor_spec with
      (\this this
         \with R
               \pre this |-> semaphoreR 1$m R ** mutex_token 1$m
               \post R).

  cpp.spec "test()" as test_spec with
      (\post emp).

  Declare Instance semaphoreR_typed : Typed2 "std::__1::mutex" semaphoreR.

  Theorem test_ok : verify[module] test_spec.
  Proof. verify_spec; go.
         iExists emp. go. (* doesn't automatically split mutex_token *)
         (* we could prove this without the splittable instance by manually
       instantiating the fraction at each call to lock/unlock *)
         iFrame.
         go.
         iFrame.
         go.
         iFrame.
         go.
  Qed.
*)

End with_cpp.
