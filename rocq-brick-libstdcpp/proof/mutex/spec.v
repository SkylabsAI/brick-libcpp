Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.mutex.test_cpp. (* TODO: this should be replaced with [inc_hpp] *)

Section with_cpp.
  Context `{Σ : !cpp_logic ti Σ0}.

  (* Generic infrastructure. TODO lift this to a thread_id.v file.
     NOTE: this needs to be placed inside of a typeclass to be sound
   *)
  Parameter thread_idT : Type.
  #[global] Declare Instance thread_idT_inh : Inhabited thread_idT.
  Canonical Structure thread_idT_bi_index : biIndex := BiIndex thread_idT _ eq _.
  Parameter L_TI : ti -ml> thread_idT_bi_index.
  #[global] Declare Instance monpred_at_least_learnable I J PROP L
    : LearnEq1 (monPred_atleast (I := I) (J := J) (PROP := PROP) L).
  Notation current_thread i := (>={ L_TI } i)%I.
  (* TODO: bikeshedding about the names + package [>={ L_TI }] into a notation at least. *)
  (* TODO: theorem [|-- ∃ i, >={ L_TI } i], maybe agreement (since the order is equality, and that should be persistent? *)
  (* TODO: show how these modalities show up in Thread::create() and Thread::get_id(), so we can refine. *)
  (* TODO: this should move to some prelude. And L_TI needs to depend on some typeclass assumption that constrains [ti], just like we do in
     [fmdeps/cpp2v/coq-bluerock-nova-interface/theories/predicates/pred.v]. *)

End with_cpp.
Notation current_thread i := (>={ L_TI } i)%I.

Set Debug "-backtrace". (* Paolo: Workaround for now-fixed bug.*)
Module mutex.
Section with_cpp.
  Context `{Σ : !cpp_logic ti Σ0}.
  Context  `{MOD : test_cpp.source ⊧ σ}. (* σ is the whole program *)

  (** <<mutex_rep q γ R>> <<q>> ownership of the mutex <<γ>> with lock invariant <<R>>. *)
  Parameter mutex_rep : cQp.t -> gname -> mpred -> Rep.
  #[global] Declare Instance mutex_rep_typed : Typed3 "std::mutex" mutex_rep.
  #[global] Declare Instance mutex_rep_cfrac : CFractional2 mutex_rep.
  #[global] Declare Instance mutex_rep_ascfrac : AsCFractional2 mutex_rep.
  #[global] Declare Instance mutex_rep_cfracvalid : CFracValid2 mutex_rep.
  #[global] Declare Instance mutex_rep_timeless : Timeless3 mutex_rep.

  (* #[only(cfractional,timeless)] derive mutex_rep. *)
  (** <<mutex_token γ q>> if <<q = 1>>, then the mutex is not locked and therefore can be destroyed *)
  Parameter mutex_token : gname -> cQp.t -> mpred.
  #[only(cfracsplittable,timeless)] derive mutex_token.

  Import auto_frac auto_pick_frac.

  #[global] Declare Instance mutex_rep_learnable : LearnEqF2 mutex_rep.
  (* a resource enforcing that the thread calling unlock must be the same thread
     that owns the lock *)
  (* TODO: maybe a bigger test demonstrating the enforcement?
  minimal version: this fails (fill in the obvious stuff)

    \persist{i} >={ L_TI } i
    \pre{j} mutex_locked g j
    test_unlock(std::mutex & m) {
      m.unlock();
    }

    this succeeds:

    \persist{i} >={ L_TI } i
    \pre mutex_locked g i
    same test_unlock
   *)

  (** <<mutex_locked γ th>> means that thread <<th>> currently owns the mutex <<γ>>. *)
  Parameter mutex_locked : gname -> thread_idT -> mpred.
  Declare Instance mutex_locked_timeless : Timeless2 mutex_locked.
  Declare Instance mutex_locked_excl g : Exclusive1 (mutex_locked g).

  cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\this this
      \with R
      \pre ▷R
      \post Exists g, this |-> mutex_rep 1$m g R ** mutex_token g 1$m).

  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep q g R (* part of both pre and post *)
      \persist{i} current_thread i
      \pre mutex_token g q
      \post R ** mutex_locked g i).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep q g R (* part of both pre and post *)
      \prepost{i} current_thread i
      \pre mutex_token g q
      \post{b}[Vbool b] if b then R ** mutex_locked g i else mutex_token g q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep q g R (* part of both pre and post *)
      \persist{i} current_thread i
      \pre mutex_locked g i
      \pre ▷R
      \post mutex_token g q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \with R
      \pre{g} this |-> mutex_rep 1$m g R ** mutex_token g 1$m
      \post R).

  cpp.spec "test()" as test_spec with
     (\prepost{i} current_thread i (* TODO: make this unnecessary? *)
      \post emp).

  Theorem test_ok : verify[source] test_spec.
  Proof. verify_spec; go.
      iExists emp.
      go.
  Qed.

End with_cpp.
End mutex.

Module recursive_mutex.
Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  

(* NOTE: Invariant used to protect resource [r]
    inv (r \\// exists th n, locked th (S n)) *)

  (* recursive mutex -- ownership of the class. *)
  Parameter R : gname -> cQp.t -> Rep.
  #[only(cfractional,timeless,type_ptr="std::recursive_mutex")] derive R.

  (* #[only(cfractional,timeless)] derive mutex_rep. *)
  (** <<token γ q>> if <<q = 1>>, then the mutex is not locked and therefore can be destroyed *)
  Parameter token : gname -> cQp.t -> mpred.
  #[only(cfracsplittable,timeless)] derive token.

  (* the mask of recursive_mutex *)
  Definition mask := nroot .@ "std" .@ "recursive_mutex".

  (** <<locked γ th n>> <<th>> owns the mutex <<γ>> <<n>> times. *)
  Parameter locked : gname -> thread_idT -> nat -> mpred.
  Declare Instance mutex_locked_timeless : Timeless3 locked.
  Axiom locked_excl_same_thread : forall g th n m,
    locked g th n ** locked g th m |-- False.
  Axiom locked_excl_different_thread : forall g th th' n m,
    locked g th n ** locked g th' m |-- [| n = 0 \/ m = 0 |] ** True.

  #[global] Declare Instance threadT_eq_decision : EqDecision thread_idT.
  #[global] Declare Instance threadT_countable : Countable thread_idT.

  Parameter used_threads : gname -> gset thread_idT -> mpred.
  Axiom use_thread : forall th g m, 
    th ∉ m ->
    current_thread th ** used_threads g m |-- |==> used_threads g (m ∪ {[ th ]}) ** locked g th 0.

  cpp.spec "std::recursive_mutex::recursive_mutex()" as ctor_spec with
    (\this this
     \post Exists g, this |-> R g 1$m ** token g 1 ** used_threads g empty).

  cpp.spec "std::recursive_mutex::~recursive_mutex()" as dtor_spec with
    (\this this
     \pre{g} this |-> R g 1$m
     \pre token g 1
     \pre{ths} used_threads g ths
     \post emp).
  
  cpp.spec "std::recursive_mutex::lock()" as lock_spec with
      (\this this
       \prepost{q g} this |-> R g q (* part of both pre and post *)
       \persist{i} current_thread i
       \pre token g q
       \pre{Q} AC << ∀ n , locked g i n >> @ top \ ↑ mask , empty
                    << locked g i (S n) , COMM Q >>
       \post Q).

  cpp.spec "std::recursive_mutex::unlock()" as unlock_spec with
      (\this this
       \prepost{q g} this |-> R g q (* part of both pre and post *)
       \persist{i} current_thread i
       \pre token g q
       \pre{Q} AC << ∀ n , locked g i (S n) >> @ top \ ↑ mask , empty
                    << locked g i n , COMM Q >>
       \post Q).


  (* Alternative style:
      R γ q r ** locked γ th (S n) |--| R γ q r ** r ** was_locked γ th (S n)

      possible solution: two specs/choice in the spec for unlock: either
      {locked γ th (n+1)} unlock() {locked γ th n}
      or
      {was_locked γ th (n+2)} unlock() {locked γ th (n+1)}
*)

End with_cpp.
End recursive_mutex.
