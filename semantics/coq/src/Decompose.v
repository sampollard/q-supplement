Require Import Chart.Semantics.Config.
Require Import Chart.Semantics.ConfigEnv.
Require Import Chart.Process.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Set Nested Proofs Allowed.

Module Import Map := FMapList.Make(Nat_as_OT).
Definition Env := Map.t nat.

Module Config <: ConfigType.
  Definition S := nat.
  Definition E := Env.
  Inductive Config :=
  | U : Config
  | P : Config -> Config -> Config
  | N : S -> Config -> Config.
End Config.
Import Config.

Module CfgEnv := ConfigEnvSemantics Config.
Import CfgEnv.

(*
  Definitions:

  1. state invariants
  2. parent is read only on child's variables
  3. child traces in parent traces (nesting operator for traces)
  4. child nested in parent only shorten's traces

 *)

Inductive Dir := L : Dir | R : Dir | St : S -> Dir.

Definition Loc := list Dir.

Lemma decide_loc_eq :
  forall (loc1 loc2 : Loc), {loc1 = loc2} + {loc1 <> loc2}.
Proof.
  intros.
  do 2 decide equality.
  apply Nat_as_OT.eq_dec.
Qed.

Fixpoint find_chart (c : Chart) (loc : Loc) : option Chart :=
  match (c, loc) with
  | (Par l r, R::loc') => find_chart r loc'
  | (Par l r, L::loc') => find_chart l loc'
  | (Nest m cs, (St s)::loc') => find_chart (cs s) loc'
  | (c, nil) => Some c
  | _ => None
  end.

Fixpoint find_config (cfg : Config) (loc : Loc) : option Config :=
  match (cfg, loc) with
  | (P l r, R::loc') => find_config r loc'
  | (P l r, L::loc') => find_config l loc'
  | (N s1 cfg, (St s2)::loc') => if EqNat.eq_nat_decide s1 s2 then find_config cfg loc' else None
  | (c, nil) => Some c
  | _ => None
  end.

(* chart step at a particular location *)
Inductive chart_loc_step : Chart -> Loc -> (Config * E) -> (Config * E) -> Prop :=
| CLS_nil : forall c cfg cfg' env env',
    chart_step c (cfg, env) (cfg', env')
    -> chart_loc_step c nil (cfg, env) (cfg', env')
| CLS_Par_left : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env' loc,
    chart_loc_step ch1 loc (cfg1, env) (cfg1', env')
    -> chart_step (Par ch1 ch2) (P cfg1 cfg2, env) (P cfg1' cfg2', env')
    -> chart_loc_step (Par ch1 ch2) (L :: loc) (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CLS_Par_right : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env' loc,
    chart_loc_step ch2 loc (cfg2, env) (cfg2', env')
    -> chart_step (Par ch1 ch2) (P cfg1 cfg2, env) (P cfg1' cfg2', env')
    -> chart_loc_step (Par ch1 ch2) (R :: loc) (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CLS_Nest_inner : forall m cs x cfg env cfg' env' loc,
    (* NOTE here we don't appeal directly to chart_step because a machine_step would be incompatible
       with a child machine stepping *)
    machine_inner m x env env'
    -> chart_loc_step (cs x) loc (cfg, env) (cfg', env')
    -> chart_loc_step (Nest m cs) (St x :: loc)(N x cfg, env) (N x cfg', env').

(* any step in the parent is a step at the specified location *)
Definition unique_child_step p loc cfgenv1 cfgenv2 :=
  forall localt, chart_loc_step p localt cfgenv1 cfgenv2 -> localt = loc.

Definition writes_var x (env1 env2 : Env) := find x env1 <> find x env2.
Definition ignores_var x (env1 env2 : Env) := find x env1 = find x env2.

(* TODO this is in the stdlib for sure *)
Lemma decide_option :
  forall {A} (o1 o2 : option A),
    (forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
    -> {o1 = o2} + {o1 <> o2}.
Proof.
  intros.
  decide equality.
Qed.

(* TODO generalize this proof to any codomain that has decidable equality *)
Lemma decide_write :
  forall x env1 env2, {writes_var x env1 env2} + {ignores_var x env1 env2}.
Proof.
  intros.
  destruct (decide_option (find x env1) (find x env2)).
  decide equality.
  right; auto.
  left; auto.
Qed.

Lemma loc_step_find_chart_cons :
  forall cfg1 cfg2 env1 env2 p1 d c loc,
    chart_loc_step p1 (d :: loc) (cfg1, env1) (cfg2, env2)
    -> find_chart p1 (d :: loc) = Some c
    -> exists p2 cfg3 cfg4, chart_loc_step p2 (loc) (cfg3, env1) (cfg4, env2) /\ find_chart p2 loc = Some c.
Proof.
  intros.
  destruct p1; try inversion H; subst; eauto; destruct d; eauto; inversion H1.
Qed.

Ltac chart_step_inv :=
  match goal with | H : chart_step _ _ _ |- _ => try inversion H end.

(* a step and a nested chart imply that the config will track *)
Lemma loc_step_find_chart_find_config_l :
  forall loc p c cfg1 cfg2 env1 env2,
    chart_loc_step p loc (cfg1, env1) (cfg2, env2)
    -> find_chart p loc = Some c
    -> exists cfg1', find_config cfg1 loc = Some cfg1'.
Proof.
  intro.
  induction loc; intros;
    destruct p;
    inversion H; subst;
      try (destruct cfg1; chart_step_inv; subst);
      simpl; eauto.

  destruct (EqNat.eq_nat_decide x x) as [? | Hneq]; eauto.
  exfalso.
  apply Hneq. apply EqNat.eq_nat_refl.
Qed.

Lemma loc_step_find_chart_find_config_r :

  forall loc p c cfg1 cfg2 env1 env2,
    chart_loc_step p loc (cfg1, env1) (cfg2, env2)
    -> find_chart p loc = Some c
    -> exists cfg2', find_config cfg2 loc = Some cfg2'.
Proof.
  intro.
  induction loc; intros;
    destruct p;
    inversion H; subst;
      try (destruct cfg1; chart_step_inv; subst);
      simpl; eauto.

  destruct (EqNat.eq_nat_decide x x) as [? | Hneq]; eauto.
  exfalso.
  apply Hneq. apply EqNat.eq_nat_refl.
Qed.

Lemma loc_step_find_chart_find_config_cons :
  forall cfg1 cfg1' cfg2 env1 env2 p1 d c loc,
    chart_loc_step p1 (d :: loc) (cfg1, env1) (cfg2, env2)
    -> find_chart p1 (d :: loc) = Some c
    -> find_config cfg1 (d :: loc) = Some cfg1'
    -> exists p2 cfg3 cfg4,
        chart_loc_step p2 (loc) (cfg3, env1) (cfg4, env2)
        /\ find_chart p2 loc = Some c
        /\ find_config cfg3 loc = Some cfg1'.
Proof.
  intros.
  destruct p1; destruct cfg1;
    try inversion H; subst.

  - exists p1_1. eauto.
  - exists p1_2. eauto.
  - simpl in H0; simpl in H1.
    destruct (EqNat.eq_nat_decide s s) as [? | Hneq].
    + exists (c0 s). eauto.
    + exfalso.
      apply Hneq. apply EqNat.eq_nat_refl.
Qed.

Lemma loc_step_find_chart_find_config_chart_initial_cons :
  forall cfg1 cfg1' cfg2 env1 env2 p1 d c loc,
    chart_loc_step p1 (d :: loc) (cfg1, env1) (cfg2, env2)
    -> find_chart p1 (d :: loc) = Some c
    -> find_config cfg1 (d :: loc) = Some cfg1'
    -> chart_initial p1 (cfg1, env1)
    -> exists p2 cfg3 cfg4,
        chart_loc_step p2 (loc) (cfg3, env1) (cfg4, env2)
        /\ find_chart p2 loc = Some c
        /\ find_config cfg3 loc = Some cfg1'
        /\ chart_initial p2 (cfg3, env1).
Proof.
  intros.
  destruct p1; destruct cfg1;
    try inversion H; subst;
      try inversion H2; subst.

  - exists p1_1. exists cfg1_1, cfg1'0. eauto.
  - exists p1_2. exists cfg1_2, cfg2'. eauto.
  - simpl in H0; simpl in H1.
    destruct (EqNat.eq_nat_decide s s) as [? | Hneq].
    + exists (c0 s). exists cfg1, cfg'. eauto.
    + exfalso.
      apply Hneq. apply EqNat.eq_nat_refl.
Qed.

Lemma loc_step_cons :
  forall cfg1 cfg2 env1 env2 p1 d loc,
    chart_loc_step p1 (d :: loc) (cfg1, env1) (cfg2, env2)
    -> exists p2 cfg3 cfg4, chart_loc_step p2 (loc) (cfg3, env1) (cfg4, env2).
Proof.
  intros.
  destruct p1; try inversion H; subst; eauto.
Qed.

Lemma find_chart_cons :
  forall p1 d c loc,
    find_chart p1 (d :: loc) = Some c
    -> exists p2, find_chart p2 loc = Some c.
Proof.
  intros.
  destruct p1; try inversion H; subst; eauto; destruct d; eauto; inversion H1.
Qed.

Lemma find_config_cons :
  forall cfg1 d cfg1' loc,
    find_config cfg1 (d :: loc) = Some cfg1'
    -> exists cfg2, find_config cfg2 loc = Some cfg1'.
Proof.
  intros.
  destruct cfg1; try inversion H; subst; eauto; destruct d; eauto; inversion H1.

  destruct (EqNat.eq_nat_decide s s0); eauto.
  inversion H1.
Qed.

Lemma loc_step_child_step :
  forall loc p c cfg1 env1 cfg2 env2,
    chart_loc_step p loc (cfg1, env1) (cfg2, env2)
    -> find_chart p loc = Some c
    -> exists cfg1' cfg2', chart_step c (cfg1', env1) (cfg2', env2).
Proof.
  intros loc.
  induction loc; intros.
  - unfold find_chart in H0. simpl in H0.
    destruct p; inversion H0; subst; inversion H; eauto.
  - edestruct loc_step_find_chart_cons as (? & ? & ? & ? & ?); eauto.
Qed.

Lemma loc_step_config_child_step:
  forall loc p c cfg1 cfg1' env1 cfg2 env2,
    chart_loc_step p loc (cfg1, env1) (cfg2, env2)
    -> find_chart p loc = Some c
    -> find_config cfg1 loc = Some cfg1'
    -> exists cfg2', chart_step c (cfg1', env1) (cfg2', env2).
Proof.
  intros loc.
  induction loc; intros.
  - unfold find_chart in H0. simpl in H0.
    unfold find_config in H1. simpl in H1.
    destruct p; destruct cfg1;
      inversion H0; inversion H1; subst; inversion H; subst;
        chart_step_inv;
        eauto.

  - edestruct loc_step_find_chart_find_config_cons as (? & ? & ? & ? & ? & ?); eauto.
Qed.

(* if x is modified, then the child at loc loc is a writer and stepped *)
Definition writer x p loc :=
  forall cfg1 env1 cfg2 env2,
    writes_var x env1 env2 -> chart_loc_step p loc (cfg1, env1) (cfg2, env2).

Definition child_owns_var x p loc1 := writer x p loc1.

(* TODO initial *)
Definition chart_process c :=
  {| initial := (fun s => chart_initial c s); step := (fun s1 s2 => chart_step c s1 s2) |}.

Definition process_invariant c P x :=
  invariant (chart_process c) (fun s => match s with (cfg, env) => P (find x env) end).

Definition process_step c s1 s2 :=
  (exists t, trace (chart_process c) (s2 :: s1 :: t)).


(* a sequence of steps at a child chart can be extended by the child stepping in some parent *)
Lemma process_step_loc_step_cons :
  forall p c loc cfg1 cfg2 cfg2' cfg3 env1 env2 env3,
    process_step c (cfg1, env1) (cfg2', env2)
    -> chart_loc_step p loc (cfg2, env2) (cfg3, env3)
    -> find_chart p loc = Some c
    -> find_config cfg2 loc = Some cfg2'
    -> exists cfg3', process_step c (cfg2', env2) (cfg3', env3).
Proof.
  intros.
  destruct H as (t & H).
  edestruct loc_step_config_child_step as (cfg3' & Hstep); eauto.
  exists cfg3'.
  exists ((cfg1, env1)::t).
  simpl.
  eapply trace_to_step; eauto.
Qed.

Lemma loc_step_init_find_init:
  forall loc p c cfg1 cfg1' cfg2 env1 env2,
    chart_loc_step p loc (cfg1, env1) (cfg2, env2)
    -> initial (chart_process p) (cfg1, env1)
    -> find_chart p loc = Some c
    -> find_config cfg1 loc = Some cfg1'
    -> initial (chart_process c) (cfg1', env1).
Proof.
  intro loc.
  induction loc; intros.
  - destruct p; destruct cfg1;
      simpl in H1; inversion H1;
        simpl in H2; inversion H2; auto.
  - edestruct loc_step_find_chart_find_config_chart_initial_cons as (? & ? & ? & ? & ? & ? & ?); eauto.
Qed.


Lemma loc_step_child_step_config:
  forall loc p c cfg1 env1 cfg2 env2,
    chart_loc_step p loc (cfg1, env1) (cfg2, env2)
    -> find_chart p loc = Some c
    -> (exists cfg1' cfg2',
           chart_step c (cfg1', env1) (cfg2', env2) /\
           find_config cfg1 loc = Some cfg1' /\
           find_config cfg2 loc = Some cfg2').
Proof.
  induction loc; intros;
    edestruct loc_step_find_chart_find_config_l as (cfg1' & Hcfg1); eauto;
      edestruct loc_step_find_chart_find_config_r as (cfg2' & Hcfg2); eauto.
  - inversion H; subst.
    exists cfg1, cfg2.
    destruct p; simpl in H0; inversion H0; subst; auto;
      (split; [|split]); destruct cfg1; destruct cfg2; simpl; auto.
  - destruct a; destruct p; destruct cfg1; destruct cfg2; simpl in H0; try discriminate.
    * edestruct IHloc as (? & ? & ? & ? & ?); eauto.
      inversion H; subst; eauto.
    * edestruct IHloc as (? & ? & ? & ? & ?); eauto.
      inversion H; subst; eauto.
    * edestruct IHloc as (? & ? & ? & ? & ?); eauto; simpl.
      inversion H; subst. eauto.
      simpl in Hcfg1.
      simpl in Hcfg2.
      destruct (EqNat.eq_nat_decide s0 s);
        destruct (EqNat.eq_nat_decide s1 s); try discriminate.
      eauto.
Qed.


Definition process_invar c (P : option nat -> Prop) x : Prop :=
  forall (env1 env2 : (Env)) cfg1 cfg2,
    process_step c (cfg1, env1) (cfg2, env2)
    -> P (find x env1)
    -> P (find x env2).

Definition variable_invariant c P x :=
  invariant (chart_process c) (fun s => match s with (cfg, env) => P (find x env) end).

Definition initial_cfg c cfg :=
  exists env, initial (chart_process c) (cfg, env).

(* If a given environment is initial for the paren
   it must be initial for any entry point (initial config)
   into the child state machine, otherwise we may
   enter the child in a state that does not satisfy
   the invariant preserved under reachable states
 *)
Definition initial_env_match p c :=
  forall env cfg cfg',
    initial (chart_process p) (cfg, env)
    -> initial_cfg c cfg'
    -> initial (chart_process c) (cfg', env).

Lemma reachable_initial:
  forall {A} p, (exists (s : A), reachable p s) -> (exists (s : A), initial p s).
Proof.
  intros.
  destruct H.
  induction H; eauto.
Qed.

Definition valid c :=
  (exists s, reachable (chart_process c) s).

Lemma initial_child_cfg_child_initial:
  forall p cfg env cfg' c loc,
    chart_initial p (cfg, env)
    -> find_chart p loc = Some c
    -> find_config cfg loc = Some cfg'
    -> chart_initial c (cfg', env).
Proof.
  intro p.

  induction p; intros;

  try (inversion H; subst).
  destruct loc; simpl in H0, H1; inversion H0; inversion H1; subst. constructor.

  destruct loc; simpl in H0, H1; inversion H0; inversion H1; subst. constructor; eauto.
  destruct d; simpl in H0, H1; eauto; discriminate.

  inversion H0; subst.
  destruct loc; simpl in H0, H1. inversion H1; inversion H2; subst. constructor; auto.
  destruct d; simpl in H1, H2; try discriminate.
  destruct (eq_nat_decide x s); try discriminate.

  eapply H; eauto.
  rewrite (eq_nat_eq x s); auto.
Qed.

Lemma step_find_config_child_step :
  forall p c loc cfg env cfg' s,
    chart_step p s (cfg, env)
    -> find_chart p loc = Some c
    -> find_config cfg loc = Some cfg'
    -> chart_initial c (cfg', env) \/ chart_loc_step p loc s (cfg, env).
Proof.
  intro p.
  induction p; intros until s; intros Hstep Hfindch Hfindcfg.
  - inversion Hstep; subst.
    destruct loc; simpl in *.

    inversion Hfindch; inversion Hfindcfg; subst.
    right.
    constructor. auto.
    discriminate.
  - inversion Hstep; subst.
    destruct loc; simpl in *.

    inversion Hfindch; inversion Hfindcfg; subst.
    right.
    constructor. auto.
    destruct d eqn:Heq.

    edestruct IHp1; eauto.
    right. constructor; auto.

    edestruct IHp2; eauto.
    right. constructor; auto.
    discriminate.
  - inversion Hstep; subst.
    + destruct loc; simpl in *.
      inversion Hfindch; inversion Hfindcfg; subst.
      right.
      constructor. auto.

      destruct d eqn:Heq; try discriminate.
      destruct (eq_nat_decide x' s); try discriminate.
      apply eq_nat_eq in e; subst.

      left.
      eapply initial_child_cfg_child_initial; eauto.
    + destruct loc; simpl in *.
      right; constructor. auto.

      destruct d eqn:Heq; try discriminate.
      destruct (eq_nat_decide x s); try discriminate.
      apply eq_nat_eq in e; subst.
      edestruct H; eauto.
      right; constructor; auto.
Qed.

Lemma child_reachable :
  forall cfg1 env1 s1 p cfg1' c loc,
  reachable (chart_process p) s1 (* (cfg1, env1) *)
  -> s1 = (cfg1, env1) (* induction is blowing away destructured terms *)
  -> find_chart p loc = Some c
  -> find_config cfg1 loc = Some cfg1'
  -> valid c
  -> initial_env_match p c
  -> reachable (chart_process c) (cfg1', env1).
Proof.
  intros until loc.
  intro Hreachp.
  generalize cfg1 env1 cfg1' c loc.
  clear cfg1 env1 cfg1' c loc.
  induction Hreachp;
    intros until loc;
    intros Heq Hfindch Hfindcfg Hereach Hinit;
    rewrite Heq in *; clear Heq.
  - constructor.
    simpl in *;
      eapply initial_child_cfg_child_initial; eauto.

  - destruct x as (cfg0, env0).

    edestruct step_find_config_child_step; simpl in *; eauto.
    + constructor.
      auto.
    + edestruct loc_step_child_step_config as (cfg0' & cfg1'' & Hcstep & Hcfgl & Hcfgr); eauto.
      specialize (IHHreachp cfg0 env0 cfg0' c loc).
      eapply reachable_step.
      apply IHHreachp; eauto.
      unfold step. simpl.
      rewrite Hcfgr in Hfindcfg. inversion Hfindcfg. subst. auto.
Qed.


(**

  Limitations

    - the values of the environment must have decidable equality so that we can
      define when a write has taken place by observing a change

  Assumptions

   - [c] is located at [loc] in [p]
   - [c] owns [x], meaning if [x] is written to then [c] stepped
   - all initial environments of [p] are initial environments for _any_ entry into [c]
   - [c] is valid if it has at least one reachable state to avoid vacuously true invariants
   - [P] holds for the value of [x] in any state reachable by [c]
 *)
Theorem child_invariants_preserved :
  forall x loc p c P,
    find_chart p loc = Some c
    -> child_owns_var x p loc
    -> initial_env_match p c
    -> valid c
    -> variable_invariant c P x
    -> variable_invariant p P x.
Proof.
  unfold variable_invariant.
  unfold invariant.
  intros until c.
  intros P Hown Hfind Hinitmatch Hecreach Hinvarp s Hreach.

  generalize P Hown Hfind Hinitmatch Hecreach Hinvarp.
  generalize x loc c.
  clear P Hown Hfind Hinitmatch Hecreach Hinvarp.
  clear x loc c.
  induction Hreach;
  intros until c;
  intros P Hfind Hown Hinitmatch Hecreach Hinvarp.


  - unfold initial_env_match in Hinitmatch.
    destruct Hecreach.
    edestruct (reachable_initial (chart_process c)).
    eauto.
    destruct x as (cfg1 & env1).
    destruct x2 as (cfg2 & env2).
    specialize (Hinitmatch env1 cfg1 cfg2).
    specialize (Hinvarp (cfg2, env1)).
    apply Hinvarp.
    constructor.
    apply Hinitmatch; auto.
    exists env2. auto.

  - destruct x as (cfg1 & env1).
    destruct y as (cfg2 & env2).
    edestruct (decide_write x0 env1 env2).
    + unfold child_owns_var in Hown.
      apply (Hown cfg1 env1 cfg2 env2) in w.
      edestruct loc_step_find_chart_find_config_l as (cfg1' & Hfindcfg); eauto.
      edestruct loc_step_config_child_step as (cfg2' & Hcstep); eauto.
      eapply (Hinvarp (cfg2', env2)).
      eapply reachable_step; eauto.
      eapply child_reachable; eauto.
    + unfold ignores_var in i.
      rewrite <- i.
      eapply IHHreach; eauto.
Qed.
