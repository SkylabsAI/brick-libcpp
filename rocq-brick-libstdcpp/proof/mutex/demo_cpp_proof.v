Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.spec.
Require Import bluerock.brick.libstdcpp.mutex.demo_cpp.


Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}. (* σ is the whole program *)
  Context {has_rmutex : HasOwn mpredI (excl_authR natO)}.
  Implicit Type (s: Z).

  Record R := mk_R {
    a : Z;
    b : Z;
    y : bool;
  }.

  (* maybe simpler if we only have one layer of tele? *)
  Definition TT : tele := [tele (_ : R)].

  Definition mk (r : R) : TT :=
    {| tele_arg_head := r; tele_arg_tail := () |}.

  Definition r_of (args:TT) : R :=
    (tele_arg_head _ args).

  Definition P (this : ptr) (maybe_s:option Z) : TT -t> mpred :=
    fun (r : R) =>
       this ,, _field "C::balance_a" |-> intR 1$m r.(a) **
       this ,, _field "C::balance_b" |-> intR 1$m r.(b) **
       match maybe_s with 
       | Some s => if r.(y) then [| (r.(a)+r.(b))%Z = s |] else emp
       | None => emp end.

  Definition CR (γ : gname) (q : cQp.t) maybe_s : Rep :=
    structR "C" q **
    _field "C::mut" |-> recursive_mutex.R γ q **
    as_Rep (fun this : ptr =>
      recursive_mutex.inv_rmutex γ (∃ (r : tele_arg _), tele_app (P this maybe_s) r)).

  Definition update {TT : tele} (f : TT -t> TT)
    (x : @recursive_mutex.acquire_state TT)
    : @recursive_mutex.acquire_state TT :=
    match x with
    | recursive_mutex.NotHeld => recursive_mutex.NotHeld
    | recursive_mutex.Held n xs => recursive_mutex.Held n (tele_app f xs)
    end.

  #[global] Instance acquireable_learn γ th TT : LearnEq2 (@recursive_mutex.acquireable _ _ _ γ th TT).
    Proof. solve_learnable. Qed.

  Section A_PLUS_B_INV.

    cpp.spec "C::update_a(int)" with
      (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q s} this |-> CR γ q (Some s)
      \pre{st th n args} recursive_mutex.acquireable γ th st (TT:=TT) (P this (Some s)) **
                         [| st = recursive_mutex.Held n args |] **
                         (* [| (0 <= a (r_of args) + x)%Z |] ** (* can't transfer beyond balance *) *)
                         [| valid<"int"> (a (r_of args) + x)%Z |] (* user responsible for overflow *)
      \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (r : R) => mk $ mk_R (a r + x) (b r) false) st)
        (P this $ (Some s))).

    cpp.spec "C::update_b(int)" with
      (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q s} this |-> CR γ q (Some s)
      \pre{st th n args} recursive_mutex.acquireable γ th st (TT:=TT) (P this (Some s)) **
                         [| st = recursive_mutex.Held n args |] **
                         (* [| (0 <= b (r_of args) + x)%Z |] ** (* can't transfer beyond balance *) *)
                         [| valid<"int"> (b (r_of args) + x)%Z |] (* user responsible for overflow *)
      \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (r : R) => mk $ mk_R (a r) (b r + x) false) st)
        (P this $ (Some s))).


    Lemma update_a_ok : verify[source] "C::update_a(int)".
    Proof using MOD _Σ has_rmutex thread_info Σ σ.
      verify_spec; go.
      rewrite /CR.
      iExists _; iExists TT; iExists (P this (Some s)); iExists q; iExists th; iExists (recursive_mutex.Held n args).
      go. ego.
      rewrite /P/=. destruct args as [r[]]; simpl.
      go.
      iExists _; iExists TT. iExists (P this $ Some s)%Z; iExists q; iExists th. iExists (S n); iExists (mk $ mk_R (_ + x) _ false).
      go.
      rewrite /P/=. go.
      rewrite /P/=. go.
    Qed.

    cpp.spec "C::transfer(int)" with
      (\this this
        \arg{x} "x" (Vint x)
        \prepost{γ q s} this |-> CR γ q (Some s)
        \pre{st th} recursive_mutex.acquireable γ th st (TT:=TT) (P this $ Some s)
        \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (r : R) => mk $ mk_R (r.(a)+x) (r.(b)-x) true) st) (P this $ Some s)).

    Lemma transfer_ok : verify[source] "C::transfer(int)".
    Proof.
      verify_spec; go.
      rewrite /CR. go.
      iExists γ; iExists TT; iExists (P this $ Some s); iExists q; iExists th; iExists _. go.
      { ego. }
      assert (∃ n args, t = recursive_mutex.Held n args) as [n [args Ht]].
      {  rewrite /recursive_mutex.acquire in H. destruct st; [destruct H as [? ?] | subst]; eexists; eauto. }
      iExists γ; iExists q; iExists s; iExists n; iExists th; iExists args; go.
      subst; simpl. go.
      iSplitR; first admit.
      go. ego.
      iExists γ; iExists q; iExists s; iExists n; iExists th; iExists _; go.
      rewrite /CR/=. go.
      iSplit; last admit.
      go. iFrame.
      go.
      iSplit; first admit.
      go.
      iExists γ; iExists TT; iExists (P this $ Some s); iExists q; iExists th; iExists _; iExists _. go.
      iFrame. go.
      rewrite /recursive_mutex.acquire in H.
      destruct st.
      { 
        destruct H. inversion H; subst.
        simpl. done.
      }
      {
        inversion H; subst.
        rewrite /P/=. 
        destruct xs as [args[]].
        destruct args. simpl.
        go. iPureIntro. admit.  
      }
    Admitted.
  End A_PLUS_B_INV.

  (* original version, do not enforce a+b to stay the same when lock is not held *)
  Section A_PLUS_B_NOT_INV.
    (* FIXME need to give it another name *)
    cpp.spec "C::update_a(int)" with
      (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q None
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this None)
      \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (r : R) => mk $ mk_R (r.(a) + x) r.(b)) args) (P this None)).

    cpp.spec "C::update_b(int)" with
      (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q None
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this None)
      \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (r : R) => mk $ mk_R r.(a) (r.(b) + x)) args) (P this None)).

    Lemma update_a_ok : verify[source] "C::update_a(int)".
    Proof.
      verify_spec; go.
      rewrite /CR.
      iExists _; iExists TT; iExists (P this None); iExists q; iExists th.
      go. ego.
      destruct args.
      { simpl in *. destruct H; subst.
        go.
        rewrite /P/=. destruct x0 as [r[]]; simpl.
        go.
        iSplitR. { admit. }
        go.
        iExists γ; iExists TT; iExists (P this None); iExists q; iExists th; iExists 0; iExists (mk $ mk_R (_ + x) _).
        go. rewrite /P. go. }
      {  simpl in *. subst.
        rewrite /P/=. destruct xs as [r[]]; simpl.
        go.
        iSplitR. { admit. }
        go.
        iExists γ; iExists TT; iExists (P this None); iExists q; iExists th; iExists (S n); iExists (mk $ mk_R (_ + x) _).
        go. rewrite /P. go.
        rewrite /P. go. }
    Admitted.

    cpp.spec "C::transfer(int)" with
      (\this this
        \arg{x} "x" (Vint x)
        \prepost{γ q} this |-> CR γ q None
        \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this None)
        \post recursive_mutex.acquireable γ th (TT:=TT) (update (TT:=TT) (fun (r : R) => mk $ mk_R (r.(a)+x) (r.(b)-x)) args) (P this None)).

    Opaque recursive_mutex.acquireable.
    Lemma transfer_ok : verify[source] "C::transfer(int)".
    Proof.
      verify_spec; go.
      rewrite /CR. go.
      iExists γ; iExists TT; iExists (P this None); iExists q; iExists th; iExists _. go.
      { ego. }
      iExists γ; iExists q; iExists _; iExists th; go.
      { ego. }
      rewrite /CR.
      iExists γ; iExists q; iExists _; iExists th; go.
      iSplitL; [ | admit ].
      go.
      destruct args.
      { destruct H. subst.
        iExists γ; iExists TT; iExists (P this None); iExists q; iExists th; iExists _; iExists _. go. }
      { red in H; subst.
        iExists γ; iExists TT; iExists (P this None); iExists q; iExists th; iExists _; iExists _. go.
        destruct xs as [r[]]; simpl.
        have->: (b r + (0 - x) = b r - x)%Z by lia.
        go. }
    Admitted.
  End A_PLUS_B_NOT_INV.

End with_cpp.
