Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.inc_hpp.
Require Export bluerock.brick.libstdcpp.runtime.pred.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter mutex_rep : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive mutex_rep.
  (*
  #[global] Declare Instance mutex_rep_typed : Typed3 "std::mutex" mutex_rep.
  #[global] Declare Instance mutex_rep_cfrac : forall γ, CFractional1 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_ascfrac : forall γ, AsCFractional2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_cfracvalid : forall γ, CFracValid2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_timeless : Timeless3 mutex_rep.
  *)
  #[global] Declare Instance mutex_rep_typed : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, Typed3 "std::mutex" mutex_rep.

  (* TODO: index this by the specific mutex! Either via a mutex_gname or by making this a Rep *)
  (* TODO: why is this separate from [mutex_rep] *)
  Parameter mutex_token : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive mutex_token.
  (*
  #[global] Declare Instance mutex_token_cfrac : CFractional1 mutex_token.
  #[global] Declare Instance mutex_token_ascfrac : AsCFractional1 mutex_token.
  #[global] Declare Instance mutex_token_cfracvalid : CFracValid1 mutex_token.
  #[global] Declare Instance mutex_token_timeless : Timeless2 mutex_token.
  *)
  #[global] Declare Instance mutex_rep_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) mutex_rep).


  (** A resource enforcing that the thread calling unlock must be the same thread
      that owns the lock

  TODO: maybe a bigger test demonstrating the enforcement?
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
  Parameter mutex_locked : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> thread_idT -> mpred.
  #[only(timeless,exclusive)] derive mutex_locked.
  (*
  Declare Instance mutex_locked_timeless : Timeless2 mutex_locked.
  Declare Instance mutex_locked_excl g : Exclusive1 (mutex_locked g).
  *)

  Context `{MOD : inc_hpp.source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\this this
      \with R
      \pre ▷R
      \post Exists g, this |-> mutex_rep g 1$m R ** mutex_token g 1$m).

  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep g q R (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_token g q
      \post R ** mutex_locked g thr).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep g q R (* part of both pre and post *)
      \prepost{i} current_thread i
      \pre mutex_token g q
      \post{b}[Vbool b] if b then R ** mutex_locked g i else mutex_token g q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q R g} this |-> mutex_rep g q R (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_locked g thr
      \pre ▷R
      \post mutex_token g q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \pre{g R} this |-> mutex_rep g 1$m R ** mutex_token g 1$m
      \post R).

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

  (* how to wrap this up into an invariant abstraction *)
  Parameter rmutex_namespace : namespace.
  Context `{HasOwn mpredI (excl_authR natO)}.
  Definition inv_rmutex  (g : gname) (P : mpred) : mpred :=
    inv rmutex_namespace (Exists n, own g (●E n) ** ([|n = 0|] ** P ** own g (◯E n) \\// [|n > 0|] ** Exists th, locked g th n)).

  Definition acquireable (g : gname) (th : thread_idT) (n : nat) (P : mpred) : mpred :=
    (P ** own g (◯E n)  \\// [|n = 0|] ** locked g th 0).
  (* TODO: we need [| 0 < n |] to the left clause. *)

  (* this is the usable pre-condition *)
  #[ignore_missing]
  cpp.spec "rmutex_client(std::recursive_mutex&)" with
    (\arg{mut} "mut" (Vref mut)
     \persist{g P} inv_rmutex g P
     \prepost{q} mut |-> R g q
     \prepost{th n} acquireable g th n P
     \post emp).
     
     
  cpp.spec "std::recursive_mutex::lock()" as lock_spec' with
    (\this this
     \persist{g P} inv_rmutex g P
     \prepost{q} this |-> R g q
     \pre{th n} acquireable g th n P
     \post acquireable g th (S n) P).
  (* to prove: this is derivable from lock_spec *)
  
  cpp.spec "std::recursive_mutex::unlock()" as unlock_spec' with
    (\this this
     \persist{g P} inv_rmutex g P
     \prepost{q} this |-> R g q
     \pre{th n} acquireable g th (S n) P
     \post acquireable g th n P).

(* potential examples that demos recursive mutex (over regular mutex) *)
cpp.prog source prog {{
  class C {
    std::recursive_mutex& mut;
    int balance_a;
    int balance_b;

    void update_a(int x) {
      mut.lock();
      balance_a += x;
      mut.unlock();
    }

    void update_b(int x) {
      mut.lock();
      balance_b += x;
      mut.unlock();
    }
    
    void transfer(int x) {
      mut.lock();
      update_a(x);
      update_b(-x);
      mut.unlock();
    }
  };

  struct C {
     std::recursive_mutex _mutex;
     int _x;

     int get_x() {
       _mutex.lock();
       auto t = _x;
       _mutex.unlock();
       return t;
     }

     int get_distance(std::recursive_mutex& mut) {
       _mutex.lock();
       // mess with the locked resources
       auto t = obj.get_x() + obj.get_x();
       _mutex.unlock();
       return t;
     }
  };

   struct Rectangle {
     std::recursive_mutex _mutex;
     
     int side1;
     int side2;

     void set_side1(int x) {
       _mutex.lock();
       this.side1 = x;
       _mutex.unlock();
     }

     void set_side2(int x) {
       _mutex.lock();
       this.side2 = x;
       _mutex.unlock();
     }

     void make_square(int x){
       _mutex.lock();
       set_side1(x);
       set_side1(x);
       _mutex.unlock();
     }
  };

}}.
End with_cpp.
End recursive_mutex.
