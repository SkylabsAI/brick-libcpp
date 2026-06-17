Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp_templates.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.prelude.
Require Import skylabs.brick.libstdcpp.mutex.requirements.

(* Generic specs for "unique_lock<T>" *)
NES.Begin unique_lock.
  Record M {T : Type} : Type := Mk
  { is_held : bool
  ; mutex_ptr : ptr
  ; mutex_q : Qp
  ; mutex_m : T }.
  #[global] Arguments M _ : clear implicits.
  #[only(lens)] derive M.

  (* To fix warnings on unreduced uses of [mutex_ptr] *)
  #[global] Hint Opaque mutex_ptr : sl_opacity.

  Definition mutex {T} (om : option (M T)) : ptr :=
    match om with
    | Some m => m.(mutex_ptr)
    | None => nullptr
    end.

  (* Whether the mutex has been locked. *)
  Definition owned {T} (om : option (M T)) : bool :=
    match om with
    | Some m => m.(is_held)
    | None => false
    end.

  (* [om] is [Some _] if a mutex is associated. *)
  sl.lock
  Definition R
      `{Σ : cpp_logic} {σ : genv} ty {T} mutexR `{!BasicLockable ty (T:=T) mutexR}
      (q : cQp.t) (om : option (M T)) : Rep :=
    let ulty := "std::unique_lock" .<< Atype ty >> in
    structR ulty q **
    (* _M_owns stores whether the mutex is locked. *)
    _field (ulty .:: Nid "_M_owns") |-> boolR q (owned om) **
    _field (ulty .:: Nid "_M_device") |-> ptrR<ty> q (mutex om) **
    match om with
    | None => emp
    | Some m =>
      pureR (m.(mutex_ptr) |-> mutexR (cQp.scale m.(mutex_q) q) m.(mutex_m))
    end.

  Section with_RepFor.
    Import rep.RepFor.
    Import RepScheme.

    #[global] Instance repfor `{Σ : cpp_logic} {σ : genv} ty {T} mutexR `{!BasicLockable ty (T:=T) mutexR} :
      rep.RepFor.C (Tnamed $ "std::unique_lock" .<< Atype ty >>) [ArgType.CFrac; ArgType.Constant _]
        (R ty mutexR) := {}.
  End with_RepFor.

  Module R_unfold.
    #[only(lazy_unfold(export))] derive R.
  End R_unfold.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context {σ : genv}.

    Section with_basic_lockable.
      Context `{!BasicLockable ty (T:=T) mutexR}.

      #[only(type_ptr)] derive R.
      #[only(cfracvalid)] derive R.

      (* #[global] Declare Instance R_timeless : *)
      (*   Timeless2 mutexR -> *)
      (*   Timeless2 (R ty mutexR). *)

      Section with_cfrac.
        Context `{CFrac : !CFractional1 mutexR}.
        #[local] Set Default Proof Using "CFrac".

        Fail #[only(cfractional)] derive R.

        #[global] Instance R_cfrac : CFractional1 (R ty mutexR).
        Proof. rewrite R.unlock. apply _. Qed.

        Fail #[only(ascfractional)] derive R.

        #[global] Instance R_as_cfrac : AsCFractional1 (R ty mutexR).
        Proof. solve_as_cfrac. Qed.

      End with_cfrac.
    End with_basic_lockable.

    Section with_threads.
      Context `{HAS_THREADS : !HasStdThreads Σ}.

      Context ty {mutexT mutexR} `{!BasicLockable ty (T:=mutexT) mutexR}.

      #[local] Abbreviation R := (R ty (T:=mutexT) mutexR).

      #[global] Instance: LearnEqF1 R := ltac:(solve_learnable).

      cpp.spec "std::unique_lock<$ty>::unique_lock()"
        as default_ctor_spec from source templates templates (
        \\with
        \this this
        \post this |-> R 1$m None
      ).

      cpp.spec "std::unique_lock<$ty>::unique_lock($ty&)" as lock_ctor_spec from source templates templates (
        \\with
        \this this
        \arg{mp} "" (Vptr mp)
        \pre{q m} mp |-> mutexR q$m m
        \pre{K} do_lock ty mp m K
        \post
          this |-> R 1$m (Some {| is_held := true ; mutex_ptr := mp ; mutex_q := q ; mutex_m := m |}) **
          K).

      cpp.spec "std::unique_lock<$ty>::unique_lock($ty&, std::defer_lock_t)" as lock_defer_ctor_spec from source templates templates (
        \\with
        \this this
        \arg{mp} "" (Vptr mp)
        \pre{q m} mp |-> mutexR q$m m
        \arg{def_p} "" (Vptr def_p)
        \post this |-> R 1$m (Some {| is_held := false ; mutex_ptr := mp ; mutex_q := q ; mutex_m := m |})
      ).

      cpp.spec "std::unique_lock<$ty>::unique_lock(std::unique_lock<$ty> &&)" as move_ctor_spec from source templates templates (
        \\with
        \this this
        \arg{other} "" (Vptr other)
        \pre{om} other |-> R 1$m om
        \post
          this |-> R 1$m om **
          other |-> R 1$m None
      ).

      (** Ensures the associated mutex is unlocked and the ownership
      is returned to the continuation <Q>.
      XXX: creates more wands than we'd like and hinders client proofs. *)
      Definition ensure_unlock (om : option (M mutexT)) (Q : mpred) : mpred :=
        match om with
        | Some {| is_held := is_held ; mutex_ptr := mp ; mutex_q := q ; mutex_m := m |} =>
          if is_held then
            letI* := do_unlock ty mp m in
            (* ▷ *)
            mp |-> mutexR q$m m -* Q
          else
            (* ▷ *)
            (mp |-> mutexR q$m m -* Q)
        | _ =>
          (* ▷ *)
          Q
        end%I.

      #[global] Arguments ensure_unlock /.

      cpp.spec "std::unique_lock<$ty>::~unique_lock()" as dtor_spec from source templates templates (
        \\with
        \this this
        \pre{om} this |-> R 1$m om
        \pre{K} ensure_unlock om K
        \post K).

      (** Duplicates [ensure_unlock], but proven equivalent and easier to apply, so
      comes after to be the default. *)
      cpp.spec "std::unique_lock<$ty>::~unique_lock()" as dtor_spec_alt from source templates templates (
        \\with
        \this this
        \pre{om} this |-> R 1$m om
        \pre{K}
          match om with
          | Some m =>
              if m.(is_held) then do_unlock ty m.(mutex_ptr) m.(mutex_m) K
              else K
          | _ => K
          end
        \post K **
          match om with
          | Some m => m.(mutex_ptr) |-> mutexR m.(mutex_q)$m m.(mutex_m)
          | None => emp
          end).

      (*
      Lemma dtor_spec_alt_entails_dtor_spec : dtor_spec_alt source -|- dtor_spec source.
      Proof.
        iSplit; iApply specify_mono. work with br_erefl; repeat case_match;
          try (exfalso; congruence);
          ework with br_erefl.
      Qed. *)

      cpp.spec "std::unique_lock<$ty>::operator=(std::unique_lock<$ty> &&)" as move_assign_spec_alt from source templates templates (
        \\with
        \this this
        \arg{other} "" (Vptr other)
        \pre{om1} this |-> R 1$m om1
        \pre{om2} other |-> R 1$m om2
        \persist{thr} current_thread thr
        \pre{K}
          match om1 with
          | Some m =>
              if m.(is_held) then do_unlock ty m.(mutex_ptr) m.(mutex_m) K
              else K
          | _ => K
          end
        \post[Vref this]
          this |-> R 1$m om2 **
          other |-> R 1$m None **
          K **
          match om1 with
          | Some m => m.(mutex_ptr) |-> mutexR m.(mutex_q)$m m.(mutex_m)
          | None => emp
          end
        ).

      (* unlock the associated mutex, if any, and set input as the associated mutex.
      Should be equivalent to move_assign_spec. *)
      cpp.spec "std::unique_lock<$ty>::operator=(std::unique_lock<$ty> &&)" as move_assign_spec from source templates templates (
        \\with
        \this this
        \arg{other} "" (Vptr other)
        \pre{om1} this |-> R 1$m om1
        \pre{om2} other |-> R 1$m om2
        \pre{K} ensure_unlock om1 K
        \post[Vref this]
          this |-> R 1$m om2 **
          other |-> R 1$m None **
          K
        ).
(*
      Lemma move_assign_spec_alt_entails_move_assign_spec : move_assign_spec_alt -|- move_assign_spec.
      Proof.
        iSplit; iApply specify_mono; work with br_erefl; repeat case_match;
          try (exfalso; congruence);
          ework with br_erefl.
      Qed. *)

      Abbreviation owns_lock_spec_body := (
        \this this
        \prepost{om q} this |-> R q om
        \post [Vbool (owned om)] emp) (only parsing).

      cpp.spec "std::unique_lock<$ty>::owns_lock() const" as owns_lock_spec
        from source templates templates (
          \\with
          owns_lock_spec_body).

      cpp.spec "std::unique_lock<$ty>::operator bool() const" as operator_bool_spec
        from source templates templates (
          \\with
          owns_lock_spec_body).

      cpp.spec "std::unique_lock<$ty>::mutex() const" as mutex_spec from source templates templates (
        \\with
        \this this
        \prepost{om q} this |-> R q om
        \post[Vptr (mutex om)] emp
      ).

      (* these preconditions statically rule out cases that throw exceptions, such as:
      - If there is no associated mutex, std::system_error with an error code of std::errc::operation_not_permitted.
      - If the mutex is already locked by this unique_lock (in other words, owns_lock() is true), std::system_error with an error code of std::errc::resource_deadlock_would_occur. *)
      cpp.spec "std::unique_lock<$ty>::lock()" as lock_spec from source templates templates (
        \\with
        \this this
        \pre{mm} this |-> R 1$m (Some mm)
        \require ~~ mm.(is_held)
        \pre{K} do_lock ty mm.(mutex_ptr) mm.(mutex_m) K
        \post
          this |-> R 1$m (Some (mm &: _is_held .= true)%lens) **
          K).

      cpp.spec "std::unique_lock<$ty>::unlock()" as unlock_spec from source templates templates (
        \\with
        \this this
        \pre{mm} this |-> R 1$m (Some mm)
        \require mm.(is_held)
        \pre{K} do_unlock ty mm.(mutex_ptr) mm.(mutex_m) K
        \post
          this |-> R 1$m (Some (mm &: _is_held .= false)%lens) **
          K
      ).

    End with_threads.
  End with_cpp.
NES.End unique_lock.
