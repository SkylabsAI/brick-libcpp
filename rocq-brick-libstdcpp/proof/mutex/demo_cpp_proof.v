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

  cpp.spec "C::update_a(int)" with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (a+x) b) args) (P this)).

  cpp.spec "C::update_b(int)" with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk a (b + x)) args) (P this)).

  Lemma update_a_ok : verify[source] "C::update_a(int)".
  Proof.
    verify_spec; go.
    rewrite /CR.
    iExists _; iExists TT; iExists (P this); iExists q; iExists th.
    go. ego.
    (* we know t must be in a held state *)
    rewrite /P/=.
    destruct args as [a [b []]]; simpl.
    go.
    iSplitR. { admit. (* TODO make the addition modulo arithmetic in the spec *) }
    go.
    iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists n; iExists (mk (_ + x) _).
    go. rewrite /P. go.
    rewrite /P. go.
    erewrite recursive_mutex.update_eq; last done.
    go.
  Admitted.

  cpp.spec "C::transfer(int)" with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
      \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (a+x) (b-x)) args) (P this)).

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    rewrite /CR. go.
    iExists γ; iExists TT; iExists (P this); iExists q; iExists th; iExists _. go.
    { ego. }
    iExists γ; iExists q; iExists _; iExists th; go.
    rewrite /CR.

    Import spec.recursive_mutex.
    Set Nested Proofs Allowed.
      #[program]
    Definition own_P_is_acquireable_C {TT : tele} g th n P args :=
      \cancelx
      \consuming tele_app P args
      \consuming own g (◯E (S n))
      \deduce acquireable(TT:=TT) g th (Held n args) P
      \end.
    Next Obligation.
      intros.
      rewrite /acquireable.
      go.
    Qed.
    
    Hint Resolve own_P_is_acquireable_C : br_hints.

    (* FIXME *)
    go.

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
