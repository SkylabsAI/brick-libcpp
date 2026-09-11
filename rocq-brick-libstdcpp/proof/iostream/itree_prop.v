Require Import skylabs.auto.cpp.prelude.proof. (* TODO: reduce dependency *)

Require Import skylabs.auto.hints.kont.

Require Export skylabs.brick.libstdcpp.iostream.itree.

(** A handler for events as a predicate transformer.

    Generally, this will be an <AU> that proves that <evt> is a valid next event.
 *)
Record SepHandler {PROP : bi} {evt : Type} : Type :=
  { do : propset evt -> (evt -> PROP) -> PROP
    (** This is effectively an <<AU>> that performs the event and then continues *)
  ; do_frame : forall evtP, ProperFrame (T:=[tele (_ : evt)]) (do evtP)
  ; do_ne : forall n, Proper ((≡) ==> pointwise_relation _ (dist n) ==> (dist n)) do
  }.
#[global] Arguments SepHandler _ _ : clear implicits.
#[global] Hint Opaque do : sl_opacity.


(* TODO: these should be replaced by library definitions *)
Section interp_itree.
  Context {PROP : bi}.
  Context {PROP_LATER : BiLaterContractive PROP}.

  Context {E : Type -> Type}.
  Context {Evt : Type}.
  Variable as_evt : forall {T}, E T -> T -> Evt.

  Context (SH : SepHandler PROP Evt).

  #[local]
  Definition interp_do_body {T} (K : T -> PROP) (rec : itree E T -d> PROP) : itree E T -d> PROP :=
    funI it =>
    match it with
    | Ret v => K v
    | Tau x => |> rec x
    | Do act k =>
        letI* evt := SH.(do) {[ evt | exists r, evt = as_evt act r ]} in
        ∃ r, [| evt = as_evt act r |] ∗ |> rec (k r)
    end.

  #[local]
  Instance interp_do_body_contractive {T} {K : T -> PROP} : Contractive (interp_do_body K).
  Proof using PROP_LATER.
    intros ??? Hdist x0.
    destruct x0; simpl; try eauto.
    { apply later_contractive. constructor.
      intros. apply Hdist. done. }
    { eapply do_ne => //.
      intro.
      do 3 f_equiv => //.
      apply later_contractive.
      by constructor; intros; apply Hdist. }
  Qed.

  Definition interp_itree {T} (it : itree E T) (K : T -> PROP) : PROP :=
    fixpoint (A:=_ -d> PROP) (interp_do_body K) it.

End interp_itree.
#[global] Arguments interp_itree {PROP _ E Event} as_evt SH {_} it _%_I : rename.
