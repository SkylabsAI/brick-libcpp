Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.prelude.pred.
Require Import bluerock.auto.cpp.prelude.proof.

Require Import bluerock.auto.core.hints.cancelx_notation.
Require Import iris.proofmode.tactics.

Parameter thread_idT : Type.
#[global] Declare Instance thread_idT_inh : Inhabited thread_idT.

Parameter HasStdThreads : forall `{Σ : cpp_logic}, Type.
#[global] Arguments HasStdThreads {_ _} Σ.
Existing Class HasStdThreads.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ}.

  Canonical Structure thread_idT_bi_index : biIndex := BiIndex thread_idT _ eq _.
  (** The projection of the thread from the thread information.

    NOTE: This is effectively a field of `HasStdThreads`, but since that
    is registered as an Axiom, we use another Parameter for this.
   *)
  Parameter threadTI : forall {_ : HasStdThreads Σ}, thread_info -ml> thread_idT_bi_index.

  (** [current_thread thr] means that the current thread is [thr].

      For more information on monalities, consult tls_modalities.
   *)
  Notation current_thread thr := (@monPred_atleast thread_info thread_idT_bi_index (uPredI (iResUR _Σ)) threadTI thr)%I.

  Context {HAS_THREADS : HasStdThreads Σ}.

  #[global] Declare Instance thread_id_learnable
    : LearnEq1 (monPred_atleast (PROP:=mpred) threadTI).

  Lemma current_thread_always_exists :
    ⊢ ∃ thr, current_thread thr.
  Proof.
    rewrite /monPred_atleast monPred2_embed_eq/monPred2_embed_def.
    constructor. intros ti.
    iIntros.
    iExists (ti .^ threadTI). iModIntro. simpl.
    iPureIntro. reflexivity.
  Qed.

  #[program]
  Definition learn_current_thread_from_context_C :=
    \cancelx
    \preserving{thr} current_thread thr
    \bound_existential ex_thr
    \proving current_thread ex_thr
    \instantiate ex_thr := thr
    \end@{mpred}.
  Next Obligation.
    simpl. intros. iIntros "X" (???); subst; iFrame.
  Qed.
  #[program]
  Definition learn_current_thread_C :=
    \cancelx
    \bound_existential ex_thr
    \proving current_thread ex_thr
    \deduce{thr} current_thread thr
    \instantiate ex_thr := thr
    \end@{mpred}.
  Next Obligation.
    iIntros.
    iDestruct current_thread_always_exists as (thr) "H".
    iExists thr. iFrame "H".
    iIntros; subst; eauto.
  Qed.

  (* TODO: show how these modalities show up in Thread::create() and Thread::get_id(), so we can refine. *)
  (* TODO: this should move to some prelude. And L_TI needs to depend on some typeclass assumption that constrains [ti], just like we do in
  [fmdeps/cpp2v/coq-bluerock-nova-interface/theories/predicates/pred.v]. *)

End with_cpp.

#[global] Hint Resolve learn_current_thread_from_context_C | 999 : br_opacity.
#[global] Hint Resolve learn_current_thread_C | 1000 : br_opacity.
#[global] Notation current_thread thr := (>={ threadTI } thr)%I.
