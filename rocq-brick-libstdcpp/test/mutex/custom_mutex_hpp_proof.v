(** Provisional *)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.
Require Import skylabs.brick.libstdcpp.atomic.spec.

Require Import skylabs.brick.libstdcpp.test.mutex.custom_mutex_hpp.

Module custom_mutex.

  Abbreviation N := "MyMutex"%cpp_name.


  Parameter thread_idR : ∀ `{Σ : cpp_logic, σ : genv}, cQp.t ->
    (* None if value is thread::id(), Some otherwise *)
    option thread_idT -> Rep.
  #[only(timeless)] derive thread_idR.

  Parameter owner_token_auth : ∀ `{Σ : cpp_logic}, iprop.gname -> option thread_idT -> mpred.
  Parameter owner_token_frac : ∀ `{Σ : cpp_logic}, iprop.gname -> option thread_idT -> mpred.
  #[only(timeless, exclusive)] derive owner_token_auth.
  #[only(timeless, exclusive)] derive owner_token_frac.

  Record gname : Set := MkGname
  { user_gname : iprop.gname
  ; cinv_gname : iprop.gname
  ; phys_state_gname : iprop.gname
  }.

  Definition lock_namespace : namespace := nroot .@@ "MyMutex".

  Definition locked `{Σ : cpp_logic} `{!lockG Σ} `{σ : genv}
      (γ: gname) (o_thr : option thread_idT) : Rep :=
    _field "MyMutex::m_owner" |-> thread_idR 1$m o_thr ** pureR (owner_token_frac γ.(phys_state_gname) o_thr).
  #[only(timeless, exclusive)] derive locked.

  (* Definition IR `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !recursive_mutex.lockedG Σ} (γ : gname) (q : cQp.t) : mpred :=
    ∃ x, recursive_mutex.owned_count_id_auth γ.(rec_gname) x. *)
(*
    Definition rawR `{Σ : cpp_logic, σ : genv} (owner : option thread_idT) (count : nat) : Rep :=
      structR "std::recursive_mutex" 1$m **
      _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m count. *)

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ, !lockG Σ}.

    Definition mutex_content (γ : gname) : Rep :=
      ∃ o_owner lockedb,
         _field "MyMutex::m_lock" |-> atomic.R "bool" 1$m lockedb **
         _field "MyMutex::m_owner" |-> thread_idR 1$m o_owner.

    Definition mutex_inv (this : ptr) (γ : gname) (P : mpred) : mpred :=
      ∃ b : bool,
      this ,, _field "MyMutex::m_lock" |-> atomic.R "int" 1$m (if b then 1 else 0)%Z **
      ∃ o_owner : option thread_idT,
      owner_token_auth γ.(phys_state_gname) o_owner **
      (if b then
        ∃ th, user γ.(user_gname) th ** [| o_owner = Some th |]
      else
        (* owner_token γ.(phys_state_gname) o_owner ** *)
        P **
        (** m_owner does not concern do_lock() and do_unlock(), the actual
          implementation of mutex, and does not always equal o_owner.
          It is just a resource that one can get from the invariant. *)
        this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None **
        owner_token_frac γ.(phys_state_gname) o_owner)
    .

    Definition IR (γ : gname) (q : cQp.t) (P : mpred) : Rep :=
      structR N q$m **
      as_Rep (fun this =>
        cinv lock_namespace γ.(cinv_gname) (mutex_inv this γ P) **
        cinv_own γ.(cinv_gname) q
      ).
    Hint Opaque IR : sl_opacity typeclass_instances.
    #[only(type_ptr,cfractional,ascfractional,cfracvalid)] derive IR.

    Context `{MOD : source ⊧ σ}.

    cpp.spec "MyMutex::MyMutex()" as ctor_spec with (
      \this this
      \pre{P} ▷P
      \post Exists g, this |-> IR g 1$m P ** used_threads g.(user_gname) ∅).

    cpp.spec "MyMutex::~MyMutex()" as dtor_spec with (
      \this this
      \pre{g P} this |-> IR g 1$m P ** used_threads g.(user_gname) ∅
      \post P).

    cpp.spec "MyMutex::do_lock()" as lock_spec with (
      \this this
      \prepost{q P g} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre user g.(user_gname) thr
      \prepost{q'} _global "std::memory_order_seq_cst" |-> primR "enum std::memory_order" q' (memory_order.to_val memory_order.seq_cst)
      \post (▷ P **
            this ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None) **
            owner_token_frac g.(phys_state_gname) (Some thr)).

    cpp.spec "MyMutex::do_unlock()" as unlock_spec with (
      \this this
      \prepost{q P g} this |-> IR g q P
      \persist{thr} current_thread thr
      \pre ▷P
      \pre this |-> locked g (Some thr)
      \post user g.(user_gname) thr).

    (* Axiom *)
    cpp.spec "std::this_thread::yield()" as yield_spec with (
      \post emp).

    Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

    Definition bi_later_exist_F := [FWD] @bi.later_exist.
    Definition bi_later_sep_F := [FWD] @bi.later_sep.
    Definition bi_later_sep_B := [BWD->] @bi.later_sep.
    Hint Resolve bi_later_exist_F bi_later_sep_F : br_hints.
    Import linearity.

    #[program]
    Definition do_exchange_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming user g.(user_gname) thr
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p,, o_field σ "MyMutex::m_lock") ) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 0 \/ res = 1 |]%Z **
                          if bool_decide (res = 0) then P ** owner_token_frac g.(phys_state_gname) (Some thr) **
                            p ,, _field "MyMutex::m_owner" |-> thread_idR 1$m None
                          else user g.(user_gname) thr)
                          \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M ?]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iAuIntro1. rewrite /atomic1_acc.
      rewrite {1}/IR/mutex_inv/=; work.
      wname [cinv] "#?".
      iInv lock_namespace as "?" "Hc"; work.
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first solve_ndisj.
      work.
      1: admit. (* can and should be an AC *)
      iMod "Y" as "_"; wpose "Hc"; work.
      wname [cinv] "CI".
      wname [owner_token_auth] "OA".
      wname [_ |-> atomic.R _ _ _] "FL".
      wname [_ |-> thread_idR _ _] "PF".
      wname [user _ _] "U".
      ren_hyp b bool.
      destruct b eqn:?; work. {
        iSplitL "OA FL PF"; first last. {
          iModIntro. rewrite /IR/mutex_inv. work $usenamed=true.
          auto.
        }
        work $usenamed=true with br_erefl.
        iExists true, _.
        ework $usenamed=true with br_erefl.
      }
      iDestruct "PF" as "(P & ? & OF)".
      iSplitL "FL OA U"; first last. {
        iModIntro. rewrite /IR/mutex_inv. ework $usenamed=true with br_erefl.
        auto.
        (* perform ghost update, but earlier *)
        admit.
      }
      work $usenamed=true with br_erefl.
      iExists true, _.
      ework $usenamed=true with br_erefl.
      (* should be proved by the previously mentioned ghost update *)
      admit. 
      all: fail.

      (* iSplitL "OG FO I FL"; first last. { *)
      (*   iModIntro. rewrite /IR/mutex_inv. work $usenamed=true. *)
      (*   wfocus [| _ |] "". { iPureIntro. destruct b; auto. } *)
      (*   destruct b eqn:?; work. *)
      (* } *)
      (* destruct b eqn:?. { *)
      (*   work $usenamed=true with br_erefl. *)
      (*   iExists _, true. *)
      (*   ework $usenamed=true with br_erefl. *)
      (* } *)
      (* work $usenamed=true with br_erefl. *)
      (* iExists _, true. *)
      (* ework $usenamed=true with br_erefl. *)
      (* iApply affine; last iAccu. *)
    Admitted.
    Hint Resolve do_exchange_C : sl_opacity.
    Hint Opaque locked : sl_opacity.

    Lemma test_do_lock_ok : verify[source] "MyMutex::do_lock()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wp_while (fun _ => emp); go; first by ework.
      wp_if; go.
    Qed.

    Lemma test_do_unlock_ok : verify[source] "MyMutex::do_unlock()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      iExists (user g.(user_gname) thr).
      rewrite /locked.
      work.
    Admitted.


  End with_Σ.
End custom_mutex.
