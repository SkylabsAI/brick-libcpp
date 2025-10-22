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
    (x : @recursive_mutex.acquire_state TT)
    : @recursive_mutex.acquire_state TT :=
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

  Lemma update_a_ok : verify[source] "C::update_a(int)".
  Proof.
    verify_spec; go.
    rewrite /CR.
    iExists _; iExists TT; iExists (P this); iExists q; iExists th.
    go. ego.
    destruct args.
    { simpl in *. destruct H; subst.
      go.
      rewrite /P/=. destruct x0 as [?[? []]]; simpl.
      go.
      iSplitR. { admit. }
      go.
      iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists 0; iExists (mk (_ + x) _).
      go. rewrite /P. go. }
    {  simpl in *. subst.
       rewrite /P/=. destruct xs as [a [b []]]; simpl.
       go.
       iSplitR. { admit. }
       go.
       iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists (S n); iExists (mk (_ + x) _).
       go. rewrite /P. go.
       rewrite /P. go. }
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
    destruct args.
    { destruct H. subst.
      iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists _; iExists _. go. }
    { red in H; subst.
      iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists _; iExists _. go.
      destruct xs as [a[b[]]]; simpl.
      have->: (b + (0 - x) = b - x)%Z by lia.
      go. }
  Admitted.

End with_cpp.
