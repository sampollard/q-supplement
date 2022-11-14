Require Import Chart.Util.
Require Import Chart.Semantics.Config.
Require Import Chart.Semantics.ConfigAction.
Require Import Chart.Semantics.ConfigEnv.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Module DCfg := DefaultConfig.
Module CfgAct := ConfigActionSemantics DCfg.
Module CfgEnv := ConfigEnvSemantics DCfg.

Section Equiv.
  Definition machine_initial_match mn mo :=
    forall cfg cnd e,
      (CfgAct.machine_initial mn cfg cnd /\ cnd e)
      <-> CfgEnv.machine_initial mo (cfg, e).

  Definition machine_terminal_match mn mo :=
    forall cfg cnd e,
      (CfgAct.machine_terminal mn cfg cnd /\ cnd e)
      <-> CfgEnv.machine_terminal mo (cfg, e).

  Definition machine_inner_match mn mo:=
    forall cfg act e1 e2,
      (CfgAct.machine_inner mn cfg act /\ act e1 e2)
      <-> CfgEnv.machine_inner mo cfg e1 e2.

  Definition machine_step_match mn mo :=
    forall cfg1 cfg2 act e1 e2,
      (CfgAct.machine_step mn cfg1 cfg2 act /\ act e1 e2)
      <-> CfgEnv.machine_step mo (cfg1, e1) (cfg2, e2).

  Definition machine_match mn mo :=
    machine_initial_match mn mo /\
    machine_terminal_match mn mo /\
    machine_inner_match mn mo /\
    machine_step_match mn mo.

  Inductive chart_initial_match : CfgAct.Chart -> CfgEnv.Chart -> Prop :=
  | CI_Unit_Init_Match :  chart_initial_match CfgAct.Unit CfgEnv.Unit
  | CI_Par_Init_Match : forall cn1 cn2 co1 co2,
      chart_initial_match cn1 co1 ->
      chart_initial_match cn2 co2 ->
      chart_initial_match (CfgAct.Par cn1 cn2) (CfgEnv.Par co1 co2)
  | CI_Nest_Init_Match : forall mn mo csn cso,
      machine_initial_match mn mo ->
      (forall x, chart_initial_match (csn x) (cso x)) ->
      chart_initial_match (CfgAct.Nest mn csn) (CfgEnv.Nest mo cso).

  Inductive chart_terminal_match : CfgAct.Chart -> CfgEnv.Chart -> Prop :=
  | CI_Unit_Term_Match :  chart_terminal_match CfgAct.Unit CfgEnv.Unit
  | CI_Par_Term_Match : forall cn1 cn2 co1 co2,
      chart_terminal_match cn1 co1 ->
      chart_terminal_match cn2 co2 ->
      chart_terminal_match (CfgAct.Par cn1 cn2) (CfgEnv.Par co1 co2)
  | CI_Nest_Term_Match : forall mn mo csn cso,
      machine_terminal_match mn mo ->
      (forall x, chart_terminal_match (csn x) (cso x)) ->
      chart_terminal_match (CfgAct.Nest mn csn) (CfgEnv.Nest mo cso).

  Fixpoint chart_match_structure co cn :=
    match (co, cn) with
    | (CfgEnv.Unit, CfgAct.Unit) => True
    | (CfgEnv.Par l2 r2, CfgAct.Par l1 r1) =>
      chart_match_structure l2 l1 /\ chart_match_structure r2 r1
    | (CfgEnv.Nest m2 f2, CfgAct.Nest m1 f1) =>
      machine_match m1 m2 /\ forall s, chart_match_structure (f2 s) (f1 s)
    | _ => False
    end.

  Definition chart_match cn co :=
    chart_match_structure co cn /\
    chart_initial_match cn co /\
    chart_terminal_match cn co.

  Ltac splits :=
    split; [|(splits + idtac)].

  Ltac chart_match_auto Hstruct Hinit Hterm :=
    destruct Hstruct;
    inversion Hinit;
    inversion Hterm;
    splits; auto.

  Lemma chart_terminal_match_env_act {e cn co cfg}:
    chart_match cn co
    -> CfgEnv.chart_terminal co (cfg, e)
    -> CfgAct.chart_terminal cn cfg (fun _ => CfgEnv.chart_terminal co (cfg, e)).
  Proof.
    generalize cn cfg. clear cn cfg.
    induction co; intros cn cfg (Hstruct & Hinit & Hterm) Hold ;
      destruct cn; simpl in Hstruct; (exfalso; assumption) + idtac;
        inversion Hold.

    - apply CfgAct.CT_Unit.
    - eapply CfgAct.CT_Env.
      instantiate (1:=(fun _ => CfgEnv.chart_terminal co1 (cfg1, e) /\
                                CfgEnv.chart_terminal co2 (cfg2, e))).
      + apply CfgAct.CT_Par.
        * apply IHco1; auto.
          chart_match_auto Hstruct Hinit Hterm.
        * apply IHco2; auto.
          chart_match_auto Hstruct Hinit Hterm.
      + intros; split; intros.
        * apply CfgEnv.CT_Par; auto.
        * inversion H5; auto.
    - eapply CfgAct.CT_Env.
      instantiate (1:=(fun _ => CfgEnv.machine_terminal m (x, e) /\
                                CfgEnv.chart_terminal (c x) (cfg0, e))).
      + apply CfgAct.CT_Nest.
        * destruct Hstruct as (Hmachine & ?).
          destruct Hmachine as (_ & Hmterm & _).
          eapply Hmterm; eauto.
        * apply H; auto.
          chart_match_auto Hstruct Hinit Hterm.
      + intros; split; intros.
        * apply CfgEnv.CT_Nest; auto.
        * inversion H6; split; auto.
  Qed.

  Lemma chart_initial_match_env_act {e cn co cfg}:
    chart_match cn co
    -> CfgEnv.chart_initial co (cfg, e)
    -> CfgAct.chart_initial cn cfg (fun _ => CfgEnv.chart_initial co (cfg, e)).
  Proof.
    generalize cn cfg. clear cn cfg.
    induction co; intros cn cfg (Hstruct & Hinit & Hterm) Hold;
      destruct cn; simpl in Hstruct; (exfalso; assumption) + idtac;
        inversion Hold.

    - apply CfgAct.CI_Unit.
    - eapply CfgAct.CI_Env.
      instantiate (1:=(fun _ => CfgEnv.chart_initial co1 (cfg1, e) /\
                                CfgEnv.chart_initial co2 (cfg2, e))).
      + apply CfgAct.CI_Par.
        * apply IHco1; auto.
          chart_match_auto Hstruct Hinit Hterm.
        * apply IHco2; auto.
          chart_match_auto Hstruct Hinit Hterm.
      + intros; split; intros.
        * apply CfgEnv.CI_Par; auto.
        * inversion H5; auto.
    - eapply CfgAct.CI_Env.
      instantiate (1:=(fun _ => CfgEnv.machine_initial m (x, e) /\
                                CfgEnv.chart_initial (c x) (cfg0, e))).
      + apply CfgAct.CI_Nest.
        * destruct Hstruct as (Hmachine & ?).
          destruct Hmachine as (Hminit & _).
          eapply Hminit; eauto.
        * apply H; auto.
          chart_match_auto Hstruct Hinit Hterm.
      + intros; split; intros.
        * apply CfgEnv.CI_Nest; auto.
        * inversion H6; split; auto.
  Qed.

  Theorem chart_step_env_act {co cn e1 e2 cfg1 cfg2} :
    chart_match cn co
    -> CfgEnv.chart_step co (cfg1, e1) (cfg2, e2)
    -> CfgAct.chart_step cn cfg1 cfg2 (fun _ _ => CfgEnv.chart_step co (cfg1, e1) (cfg2, e2)).
  Proof.
    intros Hmatch Hold.
    generalize cn Hmatch. clear cn Hmatch.
    dependent induction Hold;
      intros cn (Hstruct & Hinit & Hterm);
      destruct cn; simpl in Hstruct; (exfalso; assumption) + idtac.
    - constructor.
    - eapply CfgAct.CS_Env.
      + instantiate (1:=(fun _ _ => CfgEnv.chart_step ch1 (cfg0, e1) (cfg1', e2) /\
                                    CfgEnv.chart_step ch2 (cfg3, e1) (cfg2', e2))).
        constructor;
          [ eapply IHHold1
          | eapply IHHold2 ];
          eauto;
          chart_match_auto Hstruct Hinit Hterm.
      + split; intros.
        * constructor; intuition.
        * inversion H. intuition.
    - eapply CfgAct.CS_Env.
      instantiate(1:=(fun _ _ =>
                        (CfgEnv.chart_terminal (cs x) (cfg, e1) /\
                         CfgEnv.machine_step m (x, e1) (x', e2) /\
                         CfgEnv.chart_initial (cs x') (cfg', e2)))).
      destruct Hstruct as ((Hminitmatch & Hmtermmatch & Hminnermatch & Hmstepmatch) & ?).
      eapply CfgAct.CS_Nest_outer; eauto.
      + eapply Hmstepmatch; eauto.
      + apply chart_terminal_match_env_act; eauto.
        splits; eauto.
        * inversion Hinit; auto.
        * inversion Hterm; auto.
      + eapply chart_initial_match_env_act; eauto.
        splits; eauto.
        * inversion Hinit; auto.
        * inversion Hterm; auto.
      + split; intros Hfacts.
        destruct Hfacts as (? & ? & ?).
        * apply CfgEnv.CS_Nest_outer; eauto.
        * splits; eauto.
    - eapply CfgAct.CS_Env; eauto.

      instantiate(1:=(fun _ _ =>
                        CfgEnv.machine_inner m x e1 e2 /\
                        CfgEnv.chart_step (cs x) (cfg, e1) (cfg', e2))).

      eapply CfgAct.CS_Nest_inner; eauto.
      +  destruct Hstruct as ((_ & _ & Hminnermatch & Hmstepmatch) & _).
         eapply Hminnermatch; eauto.
      + apply IHHold; eauto.
        chart_match_auto Hstruct Hinit Hterm.
      + split; intros Hfacts.
        destruct Hfacts as (? & ?).
        * apply CfgEnv.CS_Nest_inner; eauto.
        * split; eauto.
  Qed.

  Lemma machine_step_act_env {e1 e2 mn mo cfg1 cfg2} {act : CfgAct.Action}:
    act e1 e2
    -> machine_match mn mo
    -> CfgAct.machine_step mn cfg1 cfg2 act
    -> CfgEnv.machine_step mo (cfg1, e1) (cfg2, e2).
  Proof.
    intros Hact Hmatch Hnew.
    destruct Hmatch as (Hinitm & Htermm & Hinnerm & Hstepm).
    destruct (Hstepm cfg1 cfg2 act e1 e2) as (Hstepold & Hstepnew).
    auto using Hstepold.
  Qed.

  Lemma machine_inner_act_env {e1 e2 mn mo cfg} {act : CfgAct.Action}:
    act e1 e2
    -> machine_match mn mo
    -> CfgAct.machine_inner mn cfg act
    -> CfgEnv.machine_inner mo cfg e1 e2.
  Proof.
    intros Hact Hmatch Hnew.
    edestruct Hmatch as (Hinitm & Htermm & Hinnerm & Hstepm).
    edestruct (Hinnerm cfg act) as (Hstepold & Hstepnew).
    eauto using Hstepold.
  Qed.

  Lemma chart_terminal_match_act_env {e cn co cfg} {p : CfgAct.Cond}:
    chart_match cn co
    -> CfgAct.chart_terminal cn cfg p
    -> p e
    -> CfgEnv.chart_terminal co (cfg, e).
  Proof.
    intros (Hstruct & Hinit & Hterm).
    intros Hnew.
    destruct (CfgAct.chart_terminal_chart_terminal_simple Hnew) as (p' & Hsimple & Hequiv).
    generalize cfg p' p Hsimple Hequiv. clear cfg p' p Hsimple Hequiv Hnew.
    induction Hterm as [| | ? ? ? ? ? ? IH ];
      intros cfg p' p Hsimple Hequiv Hcond;
      simpl in Hstruct;
      (exfalso; assumption) + idtac;
      inversion Hsimple;
      rewrite Hequiv in Hcond;
      match goal with
      | H : _ = p' |- _ => rewrite <- H in Hcond
      end;
      inversion Hinit;
      destruct Hstruct;
      constructor.

    - eapply IHHterm1; destruct Hcond as (? & _); eauto; intuition.
    - eapply IHHterm2; destruct Hcond as (_ & ?); eauto; intuition.
    - destruct Hcond.
      match goal with
      | H : machine_terminal_match _ _ |- _ => edestruct H
      end.
      eauto.
    - destruct Hcond. eapply IH; eauto; intuition.
  Qed.

  (*TODO nearly identical to the above proof *)
  Lemma chart_initial_match_act_env {e cn co cfg} {p : CfgAct.Cond}:
    chart_match cn co
    -> CfgAct.chart_initial cn cfg p
    -> p e
    -> CfgEnv.chart_initial co (cfg, e).
  Proof.
    intros (Hstruct & Hinit & Hterm).
    intros Hnew.
    destruct (CfgAct.chart_initial_chart_initial_simple Hnew) as (p' & Hsimple & Hequiv).
    generalize cfg p' p Hsimple Hequiv. clear cfg p' p Hsimple Hequiv Hnew.
    induction Hterm as [| | ? ? ? ? ? ? IH ];
      intros cfg p' p Hsimple Hequiv Hcond;
      simpl in Hstruct;
      (exfalso; assumption) + idtac;
      inversion Hsimple;
      rewrite Hequiv in Hcond;
      match goal with
      | H : _ = p' |- _ => rewrite <- H in Hcond
      end;
      inversion Hinit;
      destruct Hstruct;
      constructor.

    - eapply IHHterm1; destruct Hcond as (? & _); eauto; intuition.
    - eapply IHHterm2; destruct Hcond as (_ & ?); eauto; intuition.
    - destruct Hcond.
      match goal with
      | H : machine_initial_match _ _ |- _ => edestruct H
      end.
      eauto.
    - destruct Hcond. eapply IH; eauto; intuition.
  Qed.

  Theorem chart_step_act_env {co cn e1 e2 cfg1 cfg2} {act : CfgAct.Action} :
    chart_match cn co
    -> act e1 e2
    -> CfgAct.chart_step cn cfg1 cfg2 act
    -> CfgEnv.chart_step co (cfg1, e1) (cfg2, e2).
  Proof.
    intros (Hmatch & Hinitmatch & Htermmatch) Hact Hnew.
    apply CfgAct.chart_step_chart_step_simple in Hnew.
    destruct Hnew as (act' & Hnew & Hequiv).
    dependent induction co; destruct Hnew; try (destruct ch);
      simpl in Hmatch; (exfalso; assumption) + idtac.
    - apply CfgEnv.CS_Unit.
    - destruct Hmatch.
      inversion Hinitmatch.
      inversion Htermmatch.
      apply Hequiv in Hact.
      apply CfgEnv.CS_Par; [ destruct Hact as (Hact & _) | destruct Hact as (_ & Hact)].
      + eapply IHco1; eauto; intuition.
      + eapply IHco2; eauto; intuition.
    - destruct Hmatch as (Hmatchm & Hchildmatch).
      apply Hequiv in Hact.
      destruct Hact as (Hp & Hact & Hq).
      inversion Hinitmatch.
      inversion Htermmatch.
      apply CfgEnv.CS_Nest_outer.
      + eapply machine_step_act_env; eauto.
      + eapply chart_terminal_match_act_env; eauto.
        splits; auto.
      + eapply chart_initial_match_act_env; eauto.
        splits; auto.
    - destruct Hmatch as (Hmatchm & Hchildmatch).
      apply Hequiv in Hact.
      destruct Hact as (Hactin & Hactout).
      inversion Hinitmatch.
      inversion Htermmatch.
      apply CfgEnv.CS_Nest_inner.
      + clear Hactout. eapply machine_inner_act_env; eauto.
      + eapply H; eauto.
        intuition.
  Qed.
End Equiv.
