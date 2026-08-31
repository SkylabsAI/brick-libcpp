(** Provisional *)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.test.mutex.custom_mutex_hpp.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.
Import lock_ghost.
Require Import skylabs.brick.libstdcpp.atomic.spec.

Module custom_mutex.

  Abbreviation N := "MyMutex"%cpp_name.


  Parameter atomic_thread_idT : ∀ `{Σ : cpp_logic, σ : genv}, cQp.t -> option thread_idT -> Rep.

  Parameter exclusive_token : ∀ `{Σ : cpp_logic}, iprop.gname -> mpred.
  Parameter owner_token_auth : ∀ `{Σ : cpp_logic}, iprop.gname -> option thread_idT -> mpred.
  Parameter owner_token_frac : ∀ `{Σ : cpp_logic}, iprop.gname -> option thread_idT -> mpred.

  Record gname : Set := MkGname
  { user_gname : iprop.gname
  ; cinv_gname : iprop.gname
  ; phys_state_gname : iprop.gname
  }.

  Definition lock_namespace : namespace := nroot .@@ "MyMutex".

  Definition locked `{Σ : cpp_logic} `{!lockG Σ} (g: gname) (th : thread_idT) : mpred 
    := owner_token_auth g.(phys_state_gname) (Some th) ** user g.(user_gname) th.

  (* Definition IR `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !recursive_mutex.lockedG Σ} (γ : gname) (q : cQp.t) : mpred :=
    ∃ x, recursive_mutex.owned_count_id_auth γ.(rec_gname) x. *)
(*
    Definition rawR `{Σ : cpp_logic, σ : genv} (owner : option thread_idT) (count : nat) : Rep :=
      structR "std::recursive_mutex" 1$m **
      _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m count. *)

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !lockG Σ}.

    Definition mutex_content (γ : gname) : Rep :=
      ∃ o_owner lockedb,
         _field "MyMutex::m_lock" |-> atomic.R "bool" 1$m lockedb **
         _field "MyMutex::m_owner" |-> atomic_thread_idT 1$m o_owner.

    Definition mutex_inv (this : ptr) (γ : gname) (P : mpred) : mpred :=
      ∃ o_owner, this ,, _field "MyMutex::m_owner" |-> atomic_thread_idT 1$m o_owner **
      owner_token_frac γ.(phys_state_gname) o_owner **
      ∃ b : bool,
      this ,, _field "MyMutex::m_lock" |-> atomic.R "bool" 1$m b **
      if b then
        ∃ owner, [| Some owner = o_owner |]
      else
        owner_token_auth γ.(phys_state_gname) o_owner **
        P.

    Definition IR (γ : gname) (q : cQp.t) (P : mpred) : Rep :=
      structR N q$m **
      as_Rep (fun this =>
        cinv lock_namespace γ.(cinv_gname) (mutex_inv this γ P) **
        cinv_own γ.(cinv_gname) q
      ).

    Section proof.

      Context `{MOD : source ⊧ σ}.
      Context {HAS_THREADS : HasStdThreads Σ}.

      cpp.spec "MyMutex::MyMutex()" as ctor_spec with (
        \this this
        \pre{P} ▷P
        \post Exists g, this |-> IR g 1$m P ** used_threads g.(user_gname) ∅).

    End proof.

  End with_Σ.

End custom_mutex.
