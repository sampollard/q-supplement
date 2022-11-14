Require Import Chart.Semantics.Config.

(**
  This is the idealized version of the machine semantics that
  corresponds closely to the (currently closed-source) Haskell
  implementation. When a step is taken, requires the child agrees with
  [initial] and [terminal].

  A few notes: In the tool (QFramework), we basically synthesize the
  nesting by assuming you have the maximally disjunctive nesting. You
  can also give the inner machine's behavior explicitly.
  
  - [Record Machine] has the following:
  
    + initial states
  
    + terminal states

    + machine step.
  
    + inner state: if something going on in the nested state, restrict
      it. We don't model skip steps anywhere here, but instead at the
      top level.
  
  - S is a State. What part of the data is observable is not described
    here. The S is a "flat" notion of configuration, the name
    for the flat machine.
  
  - E is the collection of Environment variables (model variables); both
    those in the parent and in the child. E are not observables, since E
    are not labeled. Since it is not observed, we do not care about the
    trace preservation property. Env is externally shared, and so has
    a meaningful refinement proof about it. Env contains lots of other
    data.

  - [chart_step]. Chart is the statechart, [(Config * E)] is where you
    currently are. Think of Config as a "fancy" (read: nested) version
    of S.

    + [CS_Unit] is the chaos chart (can do anything).

    + [CS_Par] both child charts take child steps, and update the
      configurations accordingly. [P] is the parallel config. Note that
      this step is synchronous, since both take a step at once. The TLA
      notion of refinement requires invariance under an arbitrary number
      of stutter steps, and so this may cause concern here.
      There is no notion of fairness if you require some asynchronicity.
      Which is to say, if you add asynchronicity by adding either the
      left or right transition with a self-transition (stutter) step,
      there is no notion of fairness.

    + [CS_Nest_outer] move from state x to x'. To get out of x, you have
      to be in a terminal state in the nested chart x, (it's OK to leave
      x.) To move into x', you have to be in an initial step in x'.

    + [CS_Nest_inner]. For a particular state x, we require for any
      transition: if the child of x can make the transition, then then
      x can make the transition too.

*)

Module ConfigEnvSemantics (Cfg : ConfigType).
  Import Cfg.

  Record Machine :=
    { machine_initial : (S * E) -> Prop;
      machine_terminal : (S * E) -> Prop;
      machine_inner : S -> E -> E -> Prop;
      machine_step : (S * E) -> (S * E) -> Prop
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

  Inductive chart_initial : Chart -> (Config * E) -> Prop :=
  | CI_Unit : forall env,
      chart_initial Unit (U, env)
  | CI_Par : forall ch1 cfg1 ch2 cfg2 env,
      chart_initial ch1 (cfg1, env) ->
      chart_initial ch2 (cfg2, env) ->
      chart_initial (Par ch1 ch2) (P cfg1 cfg2, env)
  | CI_Nest : forall m cs x cfg env,
      machine_initial m (x, env) ->
      chart_initial (cs x) (cfg, env) ->
      chart_initial (Nest m cs) (N x cfg, env).

  Inductive chart_terminal : Chart -> (Config * E) -> Prop :=
  | CT_Unit : forall env,
      chart_terminal Unit (U, env)
  | CT_Par : forall ch1 cfg1 ch2 cfg2 env,
      chart_terminal ch1 (cfg1, env) ->
      chart_terminal ch2 (cfg2, env) ->
      chart_terminal (Par ch1 ch2) (P cfg1 cfg2, env)
  | CT_Nest : forall m x cs cfg env,
      machine_terminal m (x, env) ->
      chart_terminal (cs x) (cfg, env) ->
      chart_terminal (Nest m cs) (N x cfg, env).

  Inductive chart_step : Chart -> (Config * E) -> (Config * E) -> Prop :=
  | CS_Unit : forall env env',
      chart_step Unit (U, env) (U, env')
  | CS_Par : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env',
      chart_step ch1 (cfg1, env) (cfg1', env') ->
      chart_step ch2 (cfg2, env) (cfg2', env') ->
      chart_step (Par ch1 ch2) (P cfg1 cfg2, env) (P cfg1' cfg2', env')
  | CS_Nest_outer : forall m cs x cfg env x' cfg' env',
      machine_step m (x, env) (x', env') ->
      chart_terminal (cs x) (cfg, env) ->
      chart_initial (cs x') (cfg', env') ->
      chart_step (Nest m cs) (N x cfg, env) (N x' cfg', env')
  | CS_Nest_inner : forall m cs x cfg env cfg' env',
      machine_inner m x env env' ->
      chart_step (cs x) (cfg, env) (cfg', env') ->
      chart_step (Nest m cs) (N x cfg, env) (N x cfg', env').

  Inductive chart_refines : Chart -> Chart -> Prop :=
  | CR_Unit : forall ch, chart_refines Unit ch
  | CR_Par : forall chl1 chr1 chl2 chr2,
      chart_refines chl1 chl2 ->
      chart_refines chr1 chr2 ->
      chart_refines (Par chl1 chr1) (Par chl2 chr2)
  | CR_Nest : forall m cs1 cs2,
      (forall x, chart_refines (cs1 x) (cs2 x)) ->
      chart_refines (Nest m cs1) (Nest m cs2).

    Lemma chart_initial_config :
    forall ch cfg env, chart_initial ch (cfg,env) -> chart_config ch cfg.
  Proof.
    intros ch cfg env.
    generalize dependent cfg.
    induction ch; intros cfg Hi; inversion Hi; subst; clear Hi; constructor.
    apply IHch1; assumption.
    apply IHch2; assumption.
    apply H; assumption.
  Qed.

  Lemma chart_terminal_config :
    forall ch cfg env, chart_terminal ch (cfg,env) -> chart_config ch cfg.
  Proof.
    intros ch cfg env.
    generalize dependent cfg.
    induction ch; intros cfg Ht; inversion Ht; subst; clear Ht; constructor.
    apply IHch1; assumption.
    apply IHch2; assumption.
    apply H; assumption.
  Qed.


  Lemma chart_step_config :
    forall ch cfg1 env1 cfg2 env2,
      chart_step ch (cfg1,env1) (cfg2,env2) -> chart_config ch cfg1 /\ chart_config ch cfg2.
  Proof.
    intros ch cfg1 env1 cfg2 env2 Ht.
    split;
      generalize dependent cfg2;
      generalize dependent cfg1;
      induction ch; intros cfg1 cfg2 Ht;
        inversion Ht; subst; clear Ht; constructor.
    specialize (IHch1 _ _ H2); assumption.
    specialize (IHch2 _ _ H6); assumption.
    apply chart_terminal_config with env1; assumption.
    specialize (H _ _ _ H7); assumption.
    specialize (IHch1 _ _ H2); assumption.
    specialize (IHch2 _ _ H6); assumption.
    apply chart_initial_config with env2; assumption.
    specialize (H _ _ _ H7); assumption.
  Qed.
End ConfigEnvSemantics.
