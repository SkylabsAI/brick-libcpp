Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context  `{MOD : module ⊧ σ}. (* σ is the whole program *)

  Parameter mutex_rep : cQp.t -> mpred -> Rep.
  (* #[only(cfractional,timeless)] derive mutex_rep. *)
  Parameter mutex_token : cQp.t -> mpred.
  (* #[only(cfractional)] derive mutex_token. *)

  Import auto_frac auto_pick_frac.

  #[global] Declare Instance mutex_rep_learnable : LearnEqF1 mutex_rep.

  cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\this this
      \with R
      \pre ▷R
      \post this |-> mutex_rep 1$m R ** mutex_token 1$m).

  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q R} this |-> mutex_rep q R (* part of both pre and post *)
      \pre mutex_token q
      \post R).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q R} this |-> mutex_rep q R (* part of both pre and post *)
      \pre mutex_token q
      \post{b}[Vbool b] if b then R else mutex_token q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q R} this |-> mutex_rep q R (* part of both pre and post *)
      \pre ▷R
      \post mutex_token q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \with R
      \pre this |-> mutex_rep 1$m R ** mutex_token 1$m
      \post R).

  cpp.spec "test()" as test_spec with
      (\post emp).

  Declare Instance mutex_rep_typed : Typed2 "std::mutex" mutex_rep.

  Theorem test_ok : verify[module] test_spec.
  Proof. verify_spec; go.
      iExists emp. go. (* doesn't automatically split mutex_token *)
      (* we could prove this without the splittable instance by manually
        instantiating the fraction at each call to lock/unlock *)
      iFrame.
      go.
      iFrame.
      go.
  Qed.


End with_cpp.
