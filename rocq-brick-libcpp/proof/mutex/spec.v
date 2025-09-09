Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libcpp.mutex.test_cpp. (* TODO: this should be replaced with [inc_hpp] *)

Set Debug "-backtrace". (* Paolo: Workaround for now-fixed bug.*)
Section with_cpp.
  Context `{Σ : !cpp_logic ti Σ0}.

  (* Generic infrastructure. TODO lift *)
  Parameter thread_idT : Type.
  Declare Instance thread_idT_inh : Inhabited thread_idT.
  Canonical Structure thread_idT_bi_index : biIndex := BiIndex thread_idT _ eq _.
  Parameter L_TI : ti -ml> thread_idT_bi_index.

  Context  `{MOD : test_cpp.module ⊧ σ}. (* σ is the whole program *)

  Parameter mutex_rep : cQp.t -> mpred -> Rep.
  Declare Instance mutex_rep_cfrac : CFractional1 mutex_rep.
  Declare Instance mutex_rep_ascfrac : AsCFractional1 mutex_rep.
  Declare Instance mutex_rep_cfracvalid : CFracValid1 mutex_rep.
  Declare Instance mutex_rep_timeless : Timeless2 mutex_rep.
    
  (* #[only(cfractional,timeless)] derive mutex_rep. *)
  (* TODO: index this by the specific mutex! Either via a mutex_gname or by making this a Rep *)
  Parameter mutex_token : cQp.t -> mpred.
  Declare Instance mutex_token_cfrac : CFractional1 mutex_token.
  Declare Instance mutex_token_ascfrac : AsCFractional1 mutex_token.
  Declare Instance mutex_token_cfracvalid : CFracValid1 mutex_token.
  Declare Instance mutex_token_timeless : Timeless1 mutex_token.
  (* #[only(cfractional)] derive mutex_token. *)

  Import auto_frac auto_pick_frac.

  #[global] Declare Instance mutex_rep_learnable : LearnEqF1 mutex_rep.
  (* a resource enforcing that the thread calling unlock must be the same thread
     that owns the lock *)

  (* TODO: index this by the specific mutex! *)
  Parameter mutex_locked : thread_idT -> mpred.
  Declare Instance mutex_locked_timeless : Timeless1 mutex_locked.
  Declare Instance mutex_locked_excl : Exclusive1 mutex_locked.

  cpp.spec "std::__1::mutex::mutex()" as ctor_spec with
      (\this this
      \with R
      \pre ▷R
      \post this |-> mutex_rep 1$m R ** mutex_token 1$m).

  cpp.spec "std::__1::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q R} this |-> mutex_rep q R (* part of both pre and post *)
      \prepost{i} >={ L_TI } i
      \pre mutex_token q
      \post R ** mutex_locked i).

  cpp.spec "std::__1::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q R} this |-> mutex_rep q R (* part of both pre and post *)
      \prepost{i} >={ L_TI } i
      \pre mutex_token q
      \post{b}[Vbool b] if b then R ** mutex_locked i else mutex_token q).

  cpp.spec "std::__1::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q R} this |-> mutex_rep q R (* part of both pre and post *)
      \prepost{i} >={ L_TI } i
      \pre mutex_locked i
      \pre ▷R
      \post mutex_token q).

  cpp.spec "std::__1::mutex::~mutex()" as dtor_spec with
      (\this this
      \with R
      \pre this |-> mutex_rep 1$m R ** mutex_token 1$m
      \post R).

  cpp.spec "test()" as test_spec with
      (
      \prepost{i} >={ L_TI } i (* TODO: make this unnecessary? *)
      \post emp).

  Declare Instance mutex_rep_typed : Typed2 "std::__1::mutex" mutex_rep.

  Theorem test_ok : verify[module] test_spec.
  Proof. verify_spec; go.
      iExists emp.  go. (* doesn't automatically split mutex_token *)
      (* we could prove this without the splittable instance by manually
        instantiating the fraction at each call to lock/unlock *)
      iExists i.
      go.
   Fail progress iFrame.
  Admitted.

End with_cpp.
