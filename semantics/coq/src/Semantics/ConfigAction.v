Require Import Chart.Semantics.Config.
Require Import Chart.Process.
Require Import Coq.Logic.Decidable.

Module ConfigActionSemantics (Cfg : ConfigType).
  Import Cfg.
  Definition Cond := E -> Prop.
  Definition Action := E -> E -> Prop.

  Record Machine :=
    { machine_initial : S -> Cond -> Prop;
      machine_terminal : S -> Cond -> Prop;
      machine_inner : S -> Action -> Prop;
      machine_step : S -> S -> Action -> Prop
    }.

  Inductive Chart :=
  | Unit : Chart
  | Par : Chart -> Chart -> Chart
  | Nest : Machine -> (S -> Chart) -> Chart.

  Inductive chart_config : Chart -> Config -> Prop :=
  | CC_Unit : chart_config Unit U
  | CC_Par : forall chl chr sl sr,
      chart_config chl sl ->
      chart_config chr sr ->
      chart_config (Par chl chr) (P sl sr)
  | CC_Nest : forall x m cs s,
      chart_config (cs x) s ->
      chart_config (Nest m cs) (N x s).

  Inductive chart_initial : Chart -> Config -> Cond -> Prop :=
  | CI_Env : forall ch cfg p q,
      chart_initial ch cfg p ->
      (forall e, p e <-> q e) ->
      chart_initial ch cfg q
  | CI_Unit : forall p,
      chart_initial Unit U p
  | CI_Par : forall ch1 cfg1 p ch2 cfg2 q,
      chart_initial ch1 cfg1 p ->
      chart_initial ch2 cfg2 q ->
      chart_initial (Par ch1 ch2) (P cfg1 cfg2) (fun e => p e /\ q e)
  | CI_Nest : forall m f x p cfg q,
      machine_initial m x p ->
      chart_initial (f x) cfg q ->
      chart_initial (Nest m f) (N x cfg) (fun e => p e /\ q e).

  Inductive chart_initial_simple : Chart -> Config -> Cond -> Prop :=
  | CI_Unit_Simp : forall p,
      chart_initial_simple Unit U p
  | CI_Par_Simp : forall ch1 cfg1 p ch2 cfg2 q,
      chart_initial_simple ch1 cfg1 p ->
      chart_initial_simple ch2 cfg2 q ->
      chart_initial_simple (Par ch1 ch2) (P cfg1 cfg2) (fun e => p e /\ q e)
  | CI_Nest_Simp : forall m f x p cfg q,
      machine_initial m x p ->
      chart_initial_simple (f x) cfg q ->
      chart_initial_simple (Nest m f) (N x cfg) (fun e => p e /\ q e).

  Inductive chart_terminal : Chart -> Config -> Cond -> Prop :=
  | CT_Env : forall ch cfg p q,
      chart_terminal ch cfg p ->
      (forall e, p e <-> q e) ->
      chart_terminal ch cfg q
  | CT_Unit : forall p,
      chart_terminal Unit U p
  | CT_Par : forall ch1 cfg1 p ch2 cfg2 q,
      chart_terminal ch1 cfg1 p ->
      chart_terminal ch2 cfg2 q ->
      chart_terminal (Par ch1 ch2) (P cfg1 cfg2) (fun e => p e /\ q e)
  | CT_Nest : forall m f x p cfg q,
      machine_terminal m x p ->
      chart_terminal (f x) cfg q ->
      chart_terminal (Nest m f) (N x cfg) (fun e => p e /\ q e).

  Inductive chart_terminal_simple : Chart -> Config -> Cond -> Prop :=
  | CT_Unit_Simp : forall p,
      chart_terminal_simple Unit U p
  | CT_Par_Simp : forall ch1 cfg1 p ch2 cfg2 q,
      chart_terminal_simple ch1 cfg1 p ->
      chart_terminal_simple ch2 cfg2 q ->
      chart_terminal_simple (Par ch1 ch2) (P cfg1 cfg2) (fun e => p e /\ q e)
  | CT_Nest_Simp : forall m f x p cfg q,
      machine_terminal m x p ->
      chart_terminal_simple (f x) cfg q ->
      chart_terminal_simple (Nest m f) (N x cfg) (fun e => p e /\ q e).

  Inductive chart_step : Chart -> Config -> Config -> Action -> Prop :=
  | CS_Env : forall ch cfg cfg' act1 (act2 : E -> E -> Prop),
      chart_step ch cfg cfg' act1 ->
      (forall e e', act1 e e' <-> act2 e e') ->
      chart_step ch cfg cfg' act2
  | CS_Unit : forall act,
      chart_step Unit U U act
  | CS_Par : forall ch1 cfg1 cfg1' act1 ch2 cfg2 cfg2' act2,
      chart_step ch1 cfg1 cfg1' act1 ->
      chart_step ch2 cfg2 cfg2' act2 ->
      chart_step (Par ch1 ch2) (P cfg1 cfg2) (P cfg1' cfg2')
                 (fun e e' => act1 e e' /\ act2 e e')
  | CS_Nest_outer : forall m f x x' act cfg p cfg' q,
      machine_step m x x' act ->
      chart_terminal (f x) cfg p ->
      chart_initial (f x') cfg' q ->
      chart_step (Nest m f) (N x cfg) (N x' cfg')
                 (fun e e' => p e /\ act e e' /\ q e')
  | CS_Nest_inner : forall m f x act1 cfg cfg' act2,
      machine_inner m x act1 ->
      chart_step (f x) cfg cfg' act2 ->
      chart_step (Nest m f) (N x cfg) (N x cfg')
                 (fun e e' => act1 e e' /\ act2 e e').

  Inductive chart_step_simple : Chart -> Config -> Config -> Action -> Prop :=
  | CS_Unit_Simp : forall act,
      chart_step_simple Unit U U act
  | CS_Par_Simp : forall ch1 cfg1 cfg1' act1 ch2 cfg2 cfg2' act2,
      chart_step_simple ch1 cfg1 cfg1' act1 ->
      chart_step_simple ch2 cfg2 cfg2' act2 ->
      chart_step_simple (Par ch1 ch2) (P cfg1 cfg2) (P cfg1' cfg2')
                 (fun e e' => act1 e e' /\ act2 e e')
  | CS_Nest_outer_Simp : forall m f x x' act cfg p cfg' q,
      machine_step m x x' act ->
      chart_terminal (f x) cfg p ->
      chart_initial (f x') cfg' q ->
      chart_step_simple (Nest m f) (N x cfg) (N x' cfg')
                 (fun e e' => p e /\ act e e' /\ q e')
  | CS_Nest_inner_Simp : forall m f x act1 cfg cfg' act2,
      machine_inner m x act1 ->
      chart_step_simple (f x) cfg cfg' act2 ->
      chart_step_simple (Nest m f) (N x cfg) (N x cfg')
                        (fun e e' => act1 e e' /\ act2 e e').

  Inductive chart_refines : Chart -> Chart -> Prop :=
  | CR_Unit : forall ch, chart_refines Unit ch
  | CR_Par : forall chl1 chr1 chl2 chr2,
      chart_refines chl1 chl2 ->
      chart_refines chr1 chr2 ->
      chart_refines (Par chl1 chr1) (Par chl2 chr2)
  | CR_Nest : forall m cs1 cs2,
      (forall x, chart_refines (cs1 x) (cs2 x)) ->
      chart_refines (Nest m cs1) (Nest m cs2).

  Inductive config_refines : Config -> Config -> Prop :=
  | CFR_U : forall cfg, config_refines U cfg
  | CFR_P : forall cfgl1 cfgl2 cfgr1 cfgr2,
      config_refines cfgl1 cfgl2 ->
      config_refines cfgr1 cfgr2 ->
      config_refines (P cfgl1 cfgr1) (P cfgl2 cfgr2)
  | CFR_N : forall x cfg1 cfg2,
      config_refines cfg1 cfg2 ->
      config_refines (N x cfg1) (N x cfg2).

  Definition chart_process (ch : Chart) : Process (Config * E) :=
    {| initial '(cfg, e):= forall p, chart_initial ch cfg p -> p e;
       step '(cfg, e) '(cfg', e') := forall act, chart_step ch cfg cfg' act -> act e e'
    |}.


  Theorem dec_chart_config :
    forall ch cfg, decidable (chart_config ch cfg).
  Proof.
    induction ch.
    destruct cfg.
    left. constructor.
    right; intros Hcc; inversion Hcc.
    right; intros Hcc; inversion Hcc.

    destruct cfg.
    right; intros Hcc; inversion Hcc.
    specialize IHch1 with cfg1.
    specialize IHch2 with cfg2.
    destruct IHch1, IHch2.
    left; constructor; assumption.
    right; intros Hcc; inversion Hcc; subst; contradiction.
    right; intros Hcc; inversion Hcc; subst; contradiction.
    right; intros Hcc; inversion Hcc; subst; contradiction.
    right; intros Hcc; inversion Hcc.
    destruct cfg.
    right; intros Hcc; inversion Hcc.
    right; intros Hcc; inversion Hcc.
    specialize (H s cfg).
    destruct H.
    left; constructor; assumption.
    right; intros Hcc; inversion Hcc; subst; contradiction.
  Qed.

  Fixpoint chart_config_bool (ch : Chart) (s : Config) : bool :=
    match (ch,s) with
    | (Unit, U) => true
    | (Par chl chr, P sl sr) => chart_config_bool chl sl && chart_config_bool chr sr
    | (Nest m cs, N x s) => chart_config_bool (cs x) s
    | _ => false
    end.

  Theorem chart_config_bool_correct :
    forall ch s, chart_config ch s <-> chart_config_bool ch s = true.
  Proof.
    intros ch s.
    split; generalize dependent s.

    induction ch; intros s Hcc;
      inversion Hcc; subst; clear Hcc; simpl; intuition.

    induction ch; intros s Hcc;
      destruct s; inversion Hcc; subst; clear Hcc;
        match goal with
        | [ H : andb _ _ = true |- _ ] =>
          rewrite Bool.andb_true_iff in H
        | _ => idtac
        end; constructor.
    apply IHch1; intuition.
    apply IHch2; intuition.
    apply H; assumption.
  Qed.

  Lemma chart_initial_chart_initial_simple {ch c p} :
    chart_initial ch c p
    -> exists p', chart_initial_simple ch c p' /\ (forall e,  p e <-> p' e).
  Proof.
    intros Hstep.
    induction Hstep.
    - destruct IHHstep as (p' & Hsimple & Hequiv).
      exists p'.
      split; auto.
      intros.
      eapply iff_trans; eauto.
      split; apply H.
    - exists p.
      split; [ constructor | intuition ].
    - destruct IHHstep1 as (p1 & ? & IHequiv1).
      destruct IHHstep2 as (p2 & ? & IHequiv2).
      exists (fun e => p1 e /\ p2 e).
      split.
      + constructor; eauto.
      + split;
          intros (? & ?);
          (split; [ apply IHequiv1 | apply IHequiv2 ]; auto).
    - destruct IHHstep as (act2' & IHHstep & Hequiv).
      exists (fun e => p e /\ act2' e).
      split.
      constructor; auto.
      intros.
      rewrite <- Hequiv.
      intuition.
  Qed.

  Lemma chart_initial_config :
    forall ch cfg p, chart_initial ch cfg p -> chart_config ch cfg.
  Proof.
    intros ch cfg p Hch.
    induction Hch; try constructor; assumption.
  Qed.

  Lemma chart_terminal_config :
    forall ch cfg p, chart_terminal ch cfg p -> chart_config ch cfg.
  Proof.
    intros ch cfg p Hch.
    induction Hch; try constructor; assumption.
  Qed.

  Lemma chart_terminal_chart_terminal_simple {ch c p} :
    chart_terminal ch c p
    -> exists p', chart_terminal_simple ch c p' /\ (forall e,  p e <-> p' e).
  Proof.
    intros Hstep.
    induction Hstep.
    - destruct IHHstep as (a' & Hsimple & Hequiv).
      exists a'.
      split; auto.
      intros.
      eapply iff_trans; eauto.
      split; apply H.
    - exists p.
      split; [ constructor | intuition ].
    - destruct IHHstep1 as (p1 & ? & IHequiv1).
      destruct IHHstep2 as (p2 & ? & IHequiv2).
      exists (fun e => p1 e /\ p2 e).
      split.
      + constructor; eauto.
      + split;
          intros (? & ?);
          (split; [ apply IHequiv1 | apply IHequiv2 ]; auto).
    - destruct IHHstep as (act2' & IHHstep & Hequiv).
      exists (fun e => p e /\ act2' e).
      split.
      constructor; auto.
      intros.
      rewrite <- Hequiv.
      intuition.
  Qed.

  Lemma chart_step_chart_step_simple {ch c1 c2 a} :
    chart_step ch c1 c2 a
    -> exists a', chart_step_simple ch c1 c2 a' /\ (forall e1 e2, a e1 e2 <-> a' e1 e2).
    intros Hstep.
    induction Hstep.
    - destruct IHHstep as (a' & Hsimple & Hequiv).
      exists a'.
      split; auto.
      intros.
      eapply iff_trans; eauto.
      split; apply H.
    - exists act.
      split; [ constructor | intuition ].
    - destruct IHHstep1 as (act1' & ? & ?).
      destruct IHHstep2 as (act2' & ? & ?).
      exists (fun e1 e2 => act1' e1 e2 /\ act2' e1 e2).
      split.
      apply CS_Par_Simp; eauto.
      intros.
      split; intros.
      intuition. apply H0; auto. apply H2; auto.
      intuition. apply H0; auto. apply H2; auto.
    - exists (fun e1 e2 => p e1 /\ act e1 e2 /\ q e2).
      split.
      apply CS_Nest_outer_Simp; auto.
      intuition.
    - destruct IHHstep as (act2' & IHHstep & Hequiv).
      exists (fun e1 e2 => act1 e1 e2 /\ act2' e1 e2).
      split.
      apply CS_Nest_inner_Simp; auto.
      intros.
      rewrite <- Hequiv.
      intuition.
  Qed.

  Lemma chart_step_config :
    forall ch cfg1 cfg2 act,
      chart_step ch cfg1 cfg2 act -> chart_config ch cfg1 /\ chart_config ch cfg2.
  Proof.
    intros ch cfg1 cfg2 act Ht.
    induction Ht.
    assumption.
    split; constructor.
    split; constructor; intuition.
    split; constructor;
      [apply chart_terminal_config with p | apply chart_initial_config with q];
      assumption.
    split; constructor; intuition.
  Qed.

  (* Refinement *)

  Section Refine.
    Theorem chart_refines_refinement :
      forall ch1 ch2,
        chart_refines ch1 ch2 ->
        refinement (chart_process ch1) (chart_process ch2) eq.
    Proof.
    Abort.
  End Refine.
End ConfigActionSemantics.
