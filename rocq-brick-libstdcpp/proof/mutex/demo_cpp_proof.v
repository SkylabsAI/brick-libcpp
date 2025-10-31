Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.spec.
Require Import bluerock.brick.libstdcpp.mutex.demo_cpp.


Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}. (* σ is the whole program *)
  Context {has_rmutex : HasOwn mpredI (excl_authR natO)}.

  Definition TT : tele := [tele (_ : Z) (_ : Z)].
  Definition mk (a b : Z) : TT :=
    {| tele_arg_head := a; tele_arg_tail := {| tele_arg_head := b; tele_arg_tail := () |} |}.

  Definition P (this : ptr) : TT -t> mpred :=
    fun (a b : Z) =>
       this ,, _field "C::balance_a" |-> intR 1$m a **
       this ,, _field "C::balance_b" |-> intR 1$m b.

  Definition CR (γ : gname) (q : cQp.t) : Rep :=
    structR "C" q **
    _field "C::mut" |-> recursive_mutex.R γ q **
    as_Rep (fun this : ptr =>
      recursive_mutex.inv_rmutex γ (∃ a_b : tele_arg _, tele_app (P this) a_b)).

  Definition update {TT : tele} (f : TT -t> TT)
    (x : recursive_mutex.acquire_state TT)
    : recursive_mutex.acquire_state TT :=
    match x with
    | recursive_mutex.NotHeld => recursive_mutex.NotHeld
    | recursive_mutex.Held n xs => recursive_mutex.Held n (tele_app f xs)
    end.

  cpp.spec "C::update_a(int)" with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (a b : Z) => mk (a+x) b) args) (P this)).

  cpp.spec "C::update_b(int)" with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (a b : Z) => mk a (b + x)) args) (P this)).

  #[global] Instance acquireable_learn γ th TT : LearnEq2 (@recursive_mutex.acquireable _ _ _ γ th TT).
  Proof. solve_learnable. Qed.

  (* TODO make this into a hint *)
  Lemma is_held {t1 t2: recursive_mutex.acquire_state TT} :
    recursive_mutex.acquire t1 t2 ->
    ∃ n xs, t2 = recursive_mutex.Held n xs /\
      t1 = recursive_mutex.release t2.
  Proof.
    intros.
    destruct t1; simpl in H; eauto.
    - exists 0. naive_solver.
    - exists (S n). naive_solver.
  Qed.

  #[program]
  Definition acquireable_is_acquired_C {TT : tele} g th t t' P
      (_ : recursive_mutex.acquire (TT:=TT) t t') :=
    \cancelx
    \consuming recursive_mutex.acquireable g th t' P
    \deduce{n args} tele_app P args
    \deduce [| t' = recursive_mutex.Held n args /\ match n with 0 => t = recursive_mutex.NotHeld 
      | S n' => t = recursive_mutex.Held n' args end |]
    \end.
  Next Obligation. Admitted.

  Lemma update_a_ok : verify[source] "C::update_a(int)".
  Proof.
    verify_spec; go.
    rewrite /CR.
    iExists _; iExists TT; iExists (P this); iExists q; iExists th.
    go. ego.
    (* we know t must be in a held state *)
    destruct (is_held H) as (n & xs & -> & ?).
    simpl in *. subst.
    rewrite /P/=. destruct xs as [a [b []]]; simpl.
    go.
    iSplitR. { admit. }
    go.
    iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists n; iExists (mk (_ + x) _).
    go. rewrite /P. go.
    rewrite /P. go.
    destruct n; by subst.
  Admitted.

  cpp.spec "C::transfer(int)" with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
      \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (a b : Z) => mk (a+x) (b-x)) args) (P this)).

  Opaque recursive_mutex.acquireable.
  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    rewrite /CR. go.
    iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists _. go.
    { ego. }
    iExists γ; iExists q; iExists _; iExists th; go.
    { ego. }
    rewrite /CR.
    iExists γ; iExists q; iExists _; iExists th; go.
    iSplitL; [ | admit ].
    go.
    (* we know t must be in a held state *)
    destruct (is_held H) as (n & xs & -> & ?).
    red in H; subst.
    iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists _; iExists _. go.
    destruct xs as [a[b[]]]; simpl.
    have->: (b + (0 - x) = b - x)%Z by lia.
    destruct n; by subst.
  Admitted.

End with_cpp.
