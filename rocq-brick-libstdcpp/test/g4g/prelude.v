Require Export skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.iostream.spec.

Require Export skylabs.iris.extra.base_logic.lib.spectra.

(* BEGIN UPSTREAM *)

(* FOR SPECTRA definition *)
Class appG {evt : Type} (lts : LTS evt) (Σ : gFunctors) : Type :=
{ _has_auth_set_state : inG Σ (auth_setR (lts_state lts)) }.

Section to_spectra_mpred.
  Context `{Σ : cpp_logic}.

  #[program]
  Definition mkApp {event} (APP : LTS event) {SPECTRA : appG APP _Σ} : App.app :=
    {| App.evt := event
    ; App.lts := APP
    ; App.inG := _
    |}.
  Next Obligation.
    intros. unshelve eapply mpred_prop.mpred_has_usual_own. apply SPECTRA.
  Defined.
End to_spectra_mpred.

Section to_auto.
  Context {PROP : bi}.
  #[program]
  Definition pick_ex_C {PROP:bi}:=
    \cancelx
    \bound_existential Q
    \proving{P} (P -∗ Q)
    \instantiate Q := P
    \end@{PROP}.
  Next Obligation.
    intros.
    iIntros "_" (??? ->). iIntros "$".
  Qed.
End to_auto.
#[global] Hint Resolve pick_ex_C | 200 : sl_opacity.

Section to_cpp_auto.
  Context `{Σ : cpp_logic} {σ : genv}.
  #[program]
  Definition spec_lookup_C {fn iSpec}  :=
    \cancelx
    \preserving{P (_ : find_spec.FindSpec _ false (_global fn) P iSpec)} □ P
    \proving{spec} _global fn |-> cptrR spec
    \through [| spec = iSpec |]
    \end.
  Next Obligation.
    intros.
    iIntros "#P" (??); subst.
    destruct H.
    iDestruct (_spec_ok with "P") as "#$".
  Qed.
End to_cpp_auto.
#[global] Hint Resolve spec_lookup_C | 200 : sl_opacity.

(* FOR SPECTRA automation *)
Section operational.
  Context {T E} (step : T -> option E -> T -> Prop).

  (** [AnyStep Pre evt Post] states that the step relation can
      step from [Pre] by [evt] to the [Post].

      Note that [_steps_to] ensures that every state in [Post]
      is reachable which is necessary for soundness.
   *)
  Class AnyStep  (Pre : propset T) (evt : option E) (Post : propset T) : Prop :=
  { _non_empty : exists s, s ∈ Pre
  ; _safe : forall s, s ∈ Pre -> exists s', step s evt s' /\ s' ∈ Post
  ; _steps_to : forall s', s' ∈ Post -> ∃ s, s ∈ Pre /\ step s evt s' }.

  (** The transitive generalization of [AnyStep].

      Note: This is likely too weak to support input because it
      takes a list of fixed events rather something that allows dependency,
      e.g. such as an interaction tree.
   *)
  Inductive AnySteps (Pre : propset T) : list E -> propset T -> Prop :=
  | Finish {_ : exists s, s ∈ Pre} : AnySteps Pre [] Pre
  | Step {evt evts Mid Post}
      (_ : AnyStep Pre (Some evt) Mid)
      (_ : AnySteps Mid evts Post)
    : AnySteps Pre (evt :: evts) Post
  | Tau {evts Mid Post}
      (* Tau events are not stored in the trace *)
      (_ : AnyStep Pre None Mid)
      (_ : AnySteps Mid evts Post)
    : AnySteps Pre evts Post
  | Refine {Pre'} (_ : Pre' ⊆ Pre) {_ : exists s, s ∈ Pre'}  {es Post} :
    AnySteps Pre' es Post -> AnySteps Pre es Post.

  Lemma AnySteps_mono_post Pre evts Post Post' :
    Post' ⊆ Post ->
    (exists s, s ∈ Post') ->
    AnySteps Pre evts Post ->
    AnySteps Pre evts Post'.
  Proof. induction 3; eauto using AnySteps. Qed.

  Lemma AnySteps_mono_pre Pre' {Pre evts Post} :
    (* ∅ ⊂ Pre' ⊆ Pre ->
    AnySteps Pre evts Post ->
    AnySteps Pre' evts Post. *)
    Pre' ⊆ Pre ->
    AnySteps Pre' evts Post ->
    (exists x, x ∈ Pre') ->
    AnySteps Pre evts Post.
  Proof. intros. eapply Refine; eauto. Qed.

  Lemma AnyStep_invert_nonempty Pre evt Post :
    AnyStep Pre evt Post ->
    (exists x, x ∈ Pre) /\ (exists x, x ∈ Post).
  Proof. intros []; set_solver. Qed.

  Lemma AnySteps_invert_nonempty Pre evts Post :
    AnySteps Pre evts Post ->
    (exists x, x ∈ Pre) /\ (exists x, x ∈ Post).
  Proof.
    induction 1; intuition.
    - by destruct H.
    - by destruct H.
    - destruct H0 as [x ?]; exists x. eapply elem_of_subseteq; eauto.
  Qed.
End operational.
Existing Class AnySteps.
#[global] Hint Mode AnyStep + + + + + - : typeclass_instances.
#[global] Hint Mode AnySteps + + + + + - : typeclass_instances.


Section to_spectra.
  Context {PROP : bi}.
  Context {HAS_FUPD : BiFUpd PROP} {GHOSTLY : prop_constraints.Ghostly PROP}.
  Context `{SPECTRA : @appG evt lts Σ}.


  #[global]
  Instance requester_frame' T app E γ ps (F : (T -t> PROP) -> [tele (_:App.evt app)] -t> PROP) :
    (forall x, kont.ProperFrame (PROP:=PROP) (T:=T) (fun K => F K x)) ->
    kont.ProperFrame (PROP:=PROP) (T:=T) (fun K => Step.requester app E γ ps (F K)).
  Proof.
    intros.
    constructor.
    iIntros (??) "K H".
    rewrite /Step.requester.
    iApply (atomic_commit_ppost_wand with "[H]") => //.
    simpl.
    iIntros (? e); destruct (H e).
    iApply _frame. done.
  Qed.

  #[global]
  Instance gen_requester_frame' T app E m γ ps (F : (T -t> PROP) -> [tele (_:App.evt app)] -t> PROP) :
    (forall x, kont.ProperFrame (PROP:=PROP) (T:=T) (fun K => F K x)) ->
    kont.ProperFrame (PROP:=PROP) (T:=T) (fun K => Step.gen_requester app E m γ ps (F K)).
  Proof.
    intros.
    constructor.
    iIntros (??) "K H".
    rewrite /Step.requester.
    iApply (atomic_commit_ppost_wand with "[H]") => //.
    simpl.
    iIntros (? e); destruct (H e).
    iApply _frame. done.
  Qed.

  #[global]
  Instance requester_ne {app E γ} :
    forall n, Proper ((≡) ==> pointwise_relation _ (dist n) ==> dist n) (Step.requester app E γ).
  Proof.
    repeat intro.
    apply atomic_commit_ne => //; repeat intro;
                              repeat match goal with
                                | h : tele_arg _ |- _ => destruct h
                                end; simpl; repeat f_equiv; eauto.
    by setoid_rewrite H.
  Qed.

  #[global]
  Instance gen_requester_ne {app E m γ} :
    forall n, Proper ((≡) ==> pointwise_relation _ (dist n) ==> dist n) (Step.gen_requester app E m γ).
  Proof.
    repeat intro.
    apply atomic_commit_ne => //; repeat intro;
                              repeat match goal with
                                | h : tele_arg _ |- _ => destruct h
                                end; simpl; repeat f_equiv; eauto.
    by setoid_rewrite H.
  Qed.


  Context {T : Type} {HAS_OWN : prop_constraints.HasUsualOwn PROP (auth_setR T)}.
  Lemma frag_frag_exact  γ val :
    AuthSet.frag γ {[ val ]} ⊣⊢@{PROP} AuthSet.frag_exact γ val.
  Proof. reflexivity. Qed.
  Definition frag_frag_exact_F := [FWD<-] @frag_frag_exact.
  Definition frag_frag_exact_B := [BWD<-] @frag_frag_exact.

  #[global]
  Instance authset_frag_exact_learn {γ} :
    Cbn (Learn (learn_eq ==> learn_hints.fin) (fun x => AuthSet.frag γ {[x]})).
  Proof. clear. solve_learnable. Qed.
  Hint Resolve authset_frag_exact_learn : sl_opacity.

  Lemma use_updater APP E γ sset (_ : exists s, s ∈ sset) (_ : Step.tau_safe APP.(App.lts) sset) :
    Step.updater APP E γ
    ⊢ AuthSet.frag γ sset -∗
      |={E}=> AuthSet.frag γ {[ s' | (∃ s : lts_state (App.lts APP), s ∈ sset ∧ lts_step (App.lts APP) s None s')%type ]}.
  Proof.
    rewrite Step.updater_unseal/Step.updater_def.
    iIntros "#u".
    iApply "u"; iPureIntro; eauto.
  Qed.

  Lemma subseteq_PropSet {A} P xs : xs ⊆ PropSet P <-> forall x : A, x ∈ xs -> P x.
  Proof.
    split; intros.
    - rewrite -elem_of_PropSet; apply H; done.
    - do 2 intro. rewrite elem_of_PropSet; apply H; done.
  Qed.

  Lemma updater_anystep {_ : BiBUpdFUpd PROP} (app : App.app) ss ss' E
    (ANY_STEP : AnyStep app.(App.lts).(Sts._step) ss None ss') γ :
    AuthSet.frag γ ss
    ⊢ Step.updater app E γ -∗ |={E}=> AuthSet.frag γ ss'.
  Proof.
    iIntros "f #u".
    iDestruct (use_updater with "u f") as ">X".
    { apply ANY_STEP. }
    { intros. apply ANY_STEP in H0. destruct H0. eexists; intuition eauto. }
    iDestruct (AuthSet.frag_upd with "X") as ">$"; eauto.
    rewrite subseteq_PropSet.
    by apply ANY_STEP.
  Qed.

  Lemma requester_anystep {_ : BiBUpdFUpd PROP} (app : App.app) (s : _) s' e
    (ANY_STEP : AnyStep app.(App.lts).(Sts._step) {[s]} (Some e) s') γ :
    AuthSet.frag γ {[s]}
    ⊢ ∀ E K, (AuthSet.frag γ s' -∗ K e)%I -∗ Step.requester app E γ {[ e ]} K.
  Proof.
    intros.
    work.
    rewrite /Step.requester.
    iAcIntro.
    rewrite /commit_acc.
    simpl.
    iApply fupd_mask_intro; [ by set_solver | ].
    iIntros "Hclose".
    work.
    iExists s.
    rewrite /AuthSet.frag_exact. work.
    iSplitR.
    { iPureIntro.
      intros. destruct ANY_STEP.
      inversion H0; subst.
      edestruct _safe0; first by [].
      intuition; eauto. }
    iIntros (?) "[% Hfrag]". iMod "Hclose".
    work.
    iApply bupd_fupd.
    iDestruct (AuthSet.frag_upd with "Hfrag") as ">Hfrag"; last by iModIntro; iFrame.
    inversion ANY_STEP.
    inversion H0; subst; clear H0.
    intros ? Hin. apply _steps_to0 in Hin.
    inversion Hin as [?[??]].
    inversion H0; subst. done.
  Qed.

  (* NOTE: These definitions do not work as hints due to unfication failures *)
  #[program]
  Definition requester_C {_ : BiBUpdFUpd PROP} (app : App.app) (s : _) s' evt
    (ANY_STEP : AnyStep app.(App.lts).(Sts._step) {[s]} (Some evt) s'):=
    \cancelx
    \using{γ} AuthSet.frag γ {[s]}
    \proving{E K} Step.requester app E γ {[ evt ]} K
    \through AuthSet.frag γ s' -∗ K evt
    \end@{PROP}.
  Next Obligation. intros. by apply requester_anystep. Qed.
  Hint Resolve requester_C : sl_opacity.

  Lemma gen_requester_anystep {_ : BiBUpdFUpd PROP} (app : App.app) (s : _) s' e
    (ANY_STEP : AnyStep app.(App.lts).(Sts._step) s (Some e) s') γ :
    AuthSet.frag γ s
    ⊢ ∀ E m (_ : masks.valid m E) K, (AuthSet.frag γ s' -∗ K e)%I -∗ Step.gen_requester app E m γ {[ e ]} K.
  Proof.
    intros.
    work.
    ren_hyp Hvalid (masks.valid _ _).
    iAcIntro.
    rewrite /commit_acc.
    simpl.
    iApply fupd_mask_weaken; [| iIntros "Hclose"; iModIntro ].
    { clear -Hvalid; destruct Hvalid. set_solver. }
    work.
    iExists s. work.
    iSplitR.
    { iPureIntro. split.
      { apply AnyStep_invert_nonempty in ANY_STEP. tauto. }
      intros. destruct ANY_STEP.
      inversion H1; subst.
      edestruct _safe0; first by [].
      intuition; eauto. }
    iIntros (?) "[% Hfrag]". iMod "Hclose".
    work.
    iApply bupd_fupd.
    iDestruct (AuthSet.frag_upd with "Hfrag") as ">Hfrag"; last by iModIntro; iFrame.
    inversion ANY_STEP.
    inversion H0; subst; clear H0.
    intros ? Hin. apply _steps_to0 in Hin.
    inversion Hin as [?[??]].
    apply elem_of_PropSet. eexists; intuition eauto.
  Qed.

  #[program]
  Definition gen_requester_C {_ : BiBUpdFUpd PROP} (app : App.app) (s : _) s' evt
    (ANY_STEP : AnyStep app.(App.lts).(Sts._step) s (Some evt) s'):=
    \cancelx
    \using{γ} AuthSet.frag γ s
    \proving{E m (_ : masks.valid m E) K} Step.gen_requester app E m γ {[ evt ]} K
    \through AuthSet.frag γ s' -∗ K evt
    \end@{PROP}.
  Next Obligation. intros. erewrite gen_requester_anystep; eauto. Qed.
  Hint Resolve gen_requester_C : sl_opacity.

End to_spectra.
#[global] Hint Resolve frag_frag_exact_B frag_frag_exact_F : sl_opacity.

#[global]
Instance of_unmaterialized_refine1 `{Σ : cpp_logic} {σ : genv} {ty s s'}:
  Refine1 false true (unmaterialized_fspec ty s = unmaterialized_fspec ty s')
    [ s = s' ].
Proof.
  constructor; simpl; auto.
  inversion 1; subst; done.
Qed.

Section to_kont.
  Context {PROP : bi}.
  #[global]
  Instance as_sep_L_proper_frame {TT : tele} {P Q}
    : kont.AsSep P ->
      kont.ProperFrame (fun K : TT -t> PROP => P K ∗ Q)%I.
  Proof.
    destruct 1. constructor.
    iIntros (??) "K [P $]".
    rewrite !_as_sep.
    iDestruct "P" as (?) "[A B]".
    iExists _; iFrame "B". iApply "K"; iApply "A".
  Qed.

  #[global]
  Instance as_sep_R_proper_frame {TT : tele} {P Q}
    : kont.AsSep Q ->
      kont.ProperFrame (fun K : TT -t> PROP => P ∗ Q K)%I.
  Proof.
    destruct 1. constructor.
    iIntros (??) "K [$ P]".
    rewrite !_as_sep.
    iDestruct "P" as (?) "[A B]".
    iExists _; iFrame "B". iApply "K"; iApply "A".
  Qed.

  (* this instance is a bit of a bug when happen to end up
     finding [fun K => P ∗ K], then this can be eta-contracted to
     [bi_sep P].
   *)
  #[global]
  Instance hack_proper_frame {P}
    : kont.ProperFrame (PROP:=PROP) (T:=[tele]) (bi_sep P)%I.
  Proof.
    clear.
    constructor; simpl.
    iIntros (??) "K [$ P]".
    iApply ("K" $! ()). done.
  Qed.
End to_kont.
(* END UPSTREAM *)

Definition AppHandler {PROP : bi} {HasFupd : BiFUpd PROP} {HasGhost : prop_constraints.Ghostly PROP}
  (APP: App.app) (E : coPset) (m : masks.t) γ : SepHandler PROP (App.evt APP) :=
  {| do := Step.gen_requester APP E m γ |}%I.

Section app_handler_hints.
  Context `{Σ : cpp_logic}.
  Context `{SPECTRA : @appG evt lts _Σ}.


  #[program]
  Definition gen_bs_dos_steps_C (lts : _) inG
    (APP := {| App.evt := output_event
             ; App.lts := lts
             ; App.inG := inG |})
    (str : bs) (s s' : propset (Sts._state (App.lts _)))
    (ANY_STEPS : AnySteps APP.(App.lts).(Sts._step) s ((fun x => Write x) <$> BS.string_to_bytes str) s') :=
    \cancelx
    \using{γ} AuthSet.frag γ s
    \using Step.updater APP (⊤ ∖ ↑refinement_rootNS) γ
    \proving{K : mpredI} ostream.bs_dos (AppHandler APP (⊤ ∖ ↑refinement_rootNS) masks.default γ) str K
    \through (AuthSet.frag γ s' -∗ K)
    \end@{mpredI}.
  Next Obligation.
    clear.
    intros ? ? APP str s s' ANY_STEPS.
    remember ((fun x => Write x) <$> BS.string_to_bytes str) as X.
    generalize dependent str.
    induction ANY_STEPS; simpl.
    { destruct str; simpl; try congruence.
      intros. iIntros "[f #_]" (?) "k". iModIntro. iApply "k"; done. }
    { destruct str; simpl; try congruence.
      inversion 1; subst; intros.
      iIntros "[f #u]" (?) "k".
      eapply (gen_requester_anystep APP) in H.
      iDestruct (H with "f") as "X"; clear H.
      iModIntro.
      iApply "X".
      { iPureIntro. red. set_solver. }
      { iIntros "f". iApply (IHANY_STEPS with "[f u] k"). iFrame "#∗". } }
    { (* tau *)
      intros; subst.
      iIntros "[f #u]" (?) "k".
      rewrite ostream.bs_dos_fupd. (* TODO: shouldn't be necessary, I must have the wrong instances *)
      iDestruct ((updater_anystep APP _ _ _ H) with "f u") as ">f". iModIntro.
      iApply (IHANY_STEPS with "[f u] k").
      iFrame "#∗". }
    { intros; subst.
      iIntros "[f #u]" (?) "k".
      iDestruct (AuthSet.frag_upd with "f") as ">f"; first done.
      iApply (IHANY_STEPS with "[f u]"); iFrame "#∗". }
  Qed.

End app_handler_hints.


(** * Output Applications *)

(** The step relation for a simple LTS that uses [bs] as the state.

    This LTS only supports output transitions.
 *)
Inductive only_output : bs -> option output_event -> bs -> Prop :=
| output_char {c} {b : bs} : only_output (BS.String c b) (Some $ Write $ Byte.to_N c) b.

Definition output_app (init : bs -> Prop) : LTS output_event :=
  {| Sts._state := bs
   ; Sts._init_state := init
   ; Sts._step := only_output |}.


#[global]
Instance only_output_any_step {c cs}
  : AnyStep only_output {[ BS.String c cs ]}
      (Some $ Write $ Byte.to_N c) {[ cs ]}.
Proof.
  constructor; try inversion 1; subst.
  { set_solver. }
  { eexists; constructor => //. }
  { eexists; repeat constructor. }
Qed.

#[global]
Instance initial_any_steps {str rest : bs} :
  AnySteps only_output {[str ++ rest]}%bs
    ((λ x : N, Write x) <$> BS.string_to_bytes str)
    {[rest]}.
Proof.
  clear.
  revert rest.
  induction str.
  { constructor; set_solver. }
  { simpl.
    econstructor; [ | eapply IHstr ].
    { constructor.
      { set_solver. }
      { intros. exists (str ++ rest)%bs.
        inversion H; subst.
        have->: (BS.String b str ++ rest = BS.String b (str ++ rest))%bs by done.
        constructor => //. }
      { inversion 1; subst.
        eexists _; split.
        - set_solver.
        - constructor. } } }
Qed.

#[global]
Instance final_any_steps {str : bs} :
  AnySteps only_output {[str]}
      ((λ x : N, Write x) <$> BS.string_to_bytes str)
      {[""%bs]}.
Proof.
  intros.
  have H: str = (str ++ "")%bs by rewrite right_id.
  rewrite {1}H.
  by apply initial_any_steps.
Qed.
