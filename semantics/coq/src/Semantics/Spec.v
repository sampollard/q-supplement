Require Import Chart.Semantics.Config.
Require Import Chart.Semantics.ConfigEnv.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Import Map := FMapList.Make(Nat_as_OT).

Inductive Intent := Register | Input.
Definition Id := nat.
Definition QSpecData := list (Id * Intent).
Definition Env := Map.t nat.

(* actions are predicates the live on transitions *)
Definition Action := Env -> Env -> bool.

(* transitions are an action and the ids of the variables in the action *)
Definition Transition := (prod (list Id) (Env -> Env -> bool)).

Inductive QSpecChart :=
| Parallel : list QSpecChart -> QSpecChart
| Sequential :
    (* TODO constraints (static P(e1) P(e2), dynamic P(e1, e2))/terminal *)
    list (Transition * StateT) (* initial *)
    -> list StateT         (* TODO nonempty, unique ids *)
    -> QSpecChart

(* NOTE trying to remain faithful to the qspec stratification here
   we could make the list of states in Sequential a list of QSpecChart
   which would simplify things a bit but then would make other
   function awkward like the state mapping in the Nest chart *)
with StateT :=
| State :
    Id
    -> Action (* on entry, defaults to true, TODO option makes matching annoying in the machine_step *)
    -> Action (* on exit, defaults to true, TODO option  *)
    (* the list of transitions makes the followin simplifying assumptions:
       1. guards are actions that ignore the second env argument
       2. TODO ignoring abort and final transitions
       3. TODO ignoring priorities *)
    -> list (Transition * StateT) (* outer transitions *)
    -> list (Transition * StateT) (* inner transitions *)
    -> option QSpecChart
    -> StateT.

Definition QSpec := prod QSpecChart QSpecData.

Module Config <: ConfigType.
  Definition S := Id.
  Definition E := Env.
  Inductive Config :=
  | U : Config
  | P : Config -> Config -> Config
  | N : S -> Config -> Config.
End Config.
Import Config.

Module CfgEnv := ConfigEnvSemantics Config.
Import CfgEnv.

Fixpoint size (spec : QSpecChart) : nat :=
  match spec with
  | Parallel qs => 1 + fold_right (fun q acc => (size q) + acc) 0 qs
  | Sequential inits states =>
    1 +
    fold_right (fun s acc => match s with (a, s) => (size_statet s) + acc end) 0 inits +
    fold_right (fun s acc => size_statet s + acc) 0 states
  end
with size_statet (state : StateT) : nat :=
       match state with
       | State _ _ _ _ _ (Some q) => 1 + size q
       | State _ _ _ _ _ None => 1
       end.

Lemma z_lt_size : forall q, 0 < size q.
Proof.
  intros q. induction q; simpl; apply Nat.lt_0_succ.
Qed.


Definition trans_tuple (state : StateT) (trans : (Transition * StateT)) :=
  match trans with ((ids,a),s) => (ids, state, a, s) end.

Definition state_trans (state : StateT) : list (list Id * StateT * Action * StateT) :=
  match state with
  | State id _ _ out _ _ => List.map (trans_tuple state) out
  end.

Definition state_inner_trans (state : StateT) : list (list Id * StateT * Action * StateT) :=
  match state with
  | State id _ _ _ inner _ => List.map (trans_tuple state) inner
  end.

Definition any_prop (ps : list Prop) : Prop := fold_right or False ps.
Definition all_prop (ps : list Prop) : Prop := fold_right and True ps.

Definition match_trans (s : S) (e1 e2 : Env) (edge : (list Id * StateT * Action * StateT)) : Prop :=
  match edge with
  | (_, (State s1 _ _ _ _ _), a, (State s2 _ _ _ _ _)) => s = s1 /\ a e1 e2 = true
  end.

Definition var_eq (var : Id * Intent) (e1 e2 : Env) : Prop :=
  match var with
  | (name, Register) =>
    match (Map.find name e1, Map.find name e2) with
    | (Some v1, Some v2) => v1 = v2
    | _ => True (* TODO some part of the data does not appear in the environment *)
    end
  | (name, Input) => True
  end.

Definition regs_unchanged (exclude : list Id) (data : QSpecData) (e1 e2 : Env) : Prop :=
  (* unchanged unless we exclude them explicitly in the ids list *)
  fold_right (fun var conj => match var with | (id, intent) => (~ List.In id exclude) /\ var_eq var e1 e2 /\ conj end) True data.

Definition find_chart (chart_map : list (prod S CfgEnv.Chart)) (sid1 : S) : CfgEnv.Chart :=
  match
    List.find (fun sc => match sc with | (sid2, chart) => sid1 =? sid2 end) chart_map
  with
  | Some (_, c) => c
  | None => Unit
  end.

Fixpoint semantics (qspec : QSpecChart) (data : QSpecData) {struct qspec} : CfgEnv.Chart :=
  match qspec with
  | Parallel qs => fold_right (fun chart acc => Par (semantics chart data) acc) Unit qs
  | Sequential inits states =>
    (* trans = all the edges in the states *)
    let outer_trans := fold_right (fun s ts => ts ++ state_trans s) [] states in
    let inner_trans := fold_right (fun s ts => ts ++ state_inner_trans s) [] states in
    let chart_map := List.map (fun s =>
                                 match s with
                                 | State sid _ _ _ _ (Some qspec) => (sid, semantics qspec data)
                                 | State sid _ _ _ _ _ => (sid, Unit)
                                 end) states in
    let state_map := find_chart chart_map in
    let machine := {|
          machine_initial := (fun se =>
                                match se with
                                | (s, e) =>
                                 forall a,
                                     (* the initial transition is allowed when
                                        1. there is an edge in the initial transitions
                                        2. that edge ends at s
                                        3. the action for that edge matches on e only (a guard) TODO second env? *)
                                     (exists ids a1 a2 l1 l2 o, List.In ((ids, a), State s a1 a2 l1 l2 o) inits)
                                     /\ a e (Map.empty Id) = true
                                end);

          (* exit at any time
             TODO dual of initial
             NOTE We can use the same definition for machine_initial passing in
             the set of edges terms vs inits *)
          machine_terminal := (fun _ => True);
          machine_inner := (fun s e1 e2 =>
                              (* NOTES
                                 1. the actual implementation is guards only
                                    because checking for unsat in the inner
                                    transiton would require an existential for the
                                    next state
                                 2. the first two are in conjunction because,
                                    regardless of the user spec transition we need
                                    to maintain the behavior that it will: "only
                                    stay if it can't leave", if it was disjunction
                                    then the user spec could be "True" in which
                                    case the machine could sit in one state
                                    indefinitely regardless of out transitions that
                                    listen for signals through variables
                                 3. the final says that along with everything
                                    else if the state doesn't have a nested chart
                                    then it must maintain the register states when
                                    it does stay
                                 4. the first two could be included in the machine step
                                    where s = s1 and the last could be included there
                                    assuming when s = s1 = s2. That is, all inner
                                    transitions can be treated as normal transitions in
                                    the state's parent machine
                                    TODO, can we change (or show equivalence
                                    with) the CS_Nest_inner constructor of
                                    chart_step to remove machine_inner and
                                    use machine_step m (x, env) (x, env') (i.e a self transition)
                               *)
                              ~ (any_prop (List.map (match_trans s e1 e2) outer_trans))    (* stay step *)
                              /\ (any_prop (List.map (match_trans s e1 e2) inner_trans)) (* user spec inner transitions *)
                              /\ (state_map s = Unit -> regs_unchanged [] data e1 e2));       (* register transitions *)
                              (* TODO const_unchanged data e1 e2 *)
          machine_step := (fun se1 se2 =>
                             match (se1, se2) with
                             | ((s1, e1), (s2, e2)) =>
                                 forall ids a on_entry on_exit a1 a2 l1 l2 l3 l4 o1 o2,
                                     (* the machine steps when
                                        1. there is an edge in the transitions from s1 to s2 with action a
                                        2. that edge starts at s1 and ends at s2
                                        3. the action for that edge matches the environments
                                        4. on_(entry|exit) is/are satisfied for non-self transitions
                                        5. registers are unchanged when their ids don't appear in a
                                      *)
                                   List.In (ids, State s1 a1 on_exit l1 l2 o1, a, State s2 on_entry a2 l3 l4 o2) outer_trans
                                   /\ a e1 e2 = true
                                   /\ (on_exit e1 e2 = true)  (* for outer transitions on_exit should be true when leaving s1 *)
                                   /\ (on_entry e1 e2 = true) (* for outer transitions on_entry should be true when entering s2 *)
                                   /\ (regs_unchanged ids data e1 e2) (* Quesion: if s1 = s2 (inner transition) should on_entry fire ? *)
                             end)
        |} in
    Nest machine state_map
  end.

Lemma any_prop_in :
  forall (l : list Prop), any_prop l <-> exists P, List.In P l /\ P.
Proof.
  split; intros.
  - induction l;
      simpl in H.
    + exfalso; auto.
    + destruct H.
      * exists a.
        split; auto.
        left. auto.
      * specialize (IHl H).
        destruct IHl as (P & Hin & HP).
        exists P.
        split; auto.
        right. auto.
  - destruct H as (P & Hin & HP).
    induction l.
    + exfalso; simpl; auto.
    + simpl.
      destruct Hin.
      subst.
      left. auto.
      right.
      apply IHl.
      auto.
Qed.

Lemma outer_trans_match_trans { s1 s2 env1 env2 l a ids on_entry on_exit a1 a2 l1 l2 l3 l4 o1 o2 } :
  List.In (ids, State s1 a1 on_exit l1 l2 o1, a, State s2 on_entry a2 l3 l4 o2) l
  -> List.In (s1 = s1 /\ a env1 env2 = true) (List.map (match_trans s1 env1 env2) l).
Proof.
  intros.
  induction l.
  simpl.
  simpl in H.
  auto.
  destruct H.
  subst.
  left. auto.
  right.
  apply IHl.
  auto.
Qed.

Lemma qspec_base_must_go :
  forall qspec data m cs x1 x2 env1 env2,
    (Nest m cs) = semantics qspec data
    -> machine_step m (x1, env1) (x2, env2)
    -> ~ machine_inner m x1 env1 env2.
Proof.
  intros until env2. intros Hnest Hstep.
  destruct qspec;
    (* discharge Parallel case *)
    [destruct l;
     destruct data
    |]; simpl in Hnest; try discriminate.

  inversion Hnest; subst.
  simpl in Hstep. clear Hnest.
  simpl.
  unfold not at 1.
  intros Hinner.
  destruct Hinner as (Hstay & _).
  apply Hstay.
  clear Hstay.
  rewrite any_prop_in.
  eexists.
  split.
  - eapply outer_trans_match_trans.
    eapply Hstep.
    (* TODO so dirty *)
    Unshelve. all: (exact 1 || exact [] || exact (fun _ _ => true) || exact None).
  - split; auto.
Qed.

Lemma par_child_semantics :
  forall l r qspec data,
    Par l r = semantics qspec data
    -> (exists qspec', l = semantics qspec' data) /\
       (exists qspec', r = semantics qspec' data).
Proof.
  intros until data.
  intro Hsem; split;
    destruct qspec.
  - destruct l0. simpl in Hsem. discriminate.
    simpl in Hsem. inversion Hsem.
    eauto.
  - simpl in Hsem. discriminate.
  - destruct l0. simpl in Hsem. discriminate.
    destruct l0. simpl in Hsem. exists (Parallel []).
    simpl. inversion Hsem. auto.
    exists (Parallel (q0 :: l0)).
    simpl.
    simpl in Hsem.
    inversion Hsem.
    auto.
  - simpl in Hsem. discriminate.
Qed.

Lemma nest_machine_map_tail :
  forall m1 cs1 l l0 a data,
    Nest m1 cs1 = semantics (Sequential l (a :: l0)) data
    -> exists m2 cs2, Nest m2 cs2 = semantics (Sequential l l0) data.
Proof.
  intros.
  do 2 eexists.
  simpl.
  simpl in H. inversion H.
  f_equal.
Qed.

Set Nested Proofs Allowed.
Lemma find_chart_tail:
  forall i1 i2 l sem,
    i1 <> i2
    -> find_chart ((i1, sem) :: l) i2  = find_chart l i2.
Proof.
  intros.
  unfold find_chart. simpl.
  edestruct Nat.eqb_neq.
  erewrite H1; auto.
Qed.

Lemma nest_child_semantics :
  forall qspec data m cs s,
    Nest m cs = semantics qspec data
    -> (exists qspec', (cs s) = semantics qspec' data).
Proof.
  intros until data.
  destruct qspec.
  - intros Hsem; destruct l; simpl in Hsem; discriminate.
  - induction l0; intros m cs s Hsem.
    + simpl.
      simpl in Hsem. inversion Hsem.
      unfold find_chart.
      simpl.
      exists (Parallel []).
      auto.
    + destruct a.
      * destruct (Nat.eq_dec s i); subst.
        -- remember Hsem as Hsemsmall.
           simpl in Hsem. inversion Hsem.
           clear H0. clear H1.
           unfold find_chart.
           simpl.
           destruct o; rewrite Nat.eqb_refl.

           ++ exists q. auto.
           ++ exists (Parallel []). auto.
        -- simpl in Hsem. inversion Hsem.
           destruct o;
             (rewrite find_chart_tail; auto;
              eapply IHl0;
              simpl;
              eauto).
Qed.

Ltac force_config :=
  match goal with
  | H : chart_config (Par _ _) ?cfg |- _ => destruct cfg; inversion H; clear H
  | H : chart_config (Nest _ _) ?cfg |- _ => destruct cfg; inversion H; clear H
  | H : chart_config _ ?cfg |- _ => destruct cfg; inversion H; clear H
  end; subst.

(*
  Problem: we often want to say something about specific parts of a chart (e.g. qspec_base_must_go)
  but we should ensure that it's true no matter where such a part appears in the inductive structure
  of a larger chart.

  Previously we have done this by defining the statement itself inductively and then ensuring a
  predicate is true the point of interest. If we take the must_go example we might create two
  such inductive predicates:

  chart_machine_step :=
    chart_machine_step Unit
    | chart_machine_step s -> machine_step Nest -> chart_machine_step (Nest s)
    | chart_machine_step l -> chart_machine_step r -> chart_machine_step (Par l r)

  chart_machine_inner_step :=
    chart_machine_inner_step Unit
    | chart_machine_inner_step s -> machine_inner_step Nest -> chart_machine_inner_step (Nest s)
    | chart_machine_inner_step l -> chart_machine_inner_step r -> chart_machine_inner_step (Par l r)

  Then the theorem is something like:
  chart_machine_step -> ~ chart_machine_inner_step

  This is annoying on a few levels.

  1. The amount of typing involved may result in errors
  2. The structure of bothe statements is identical except for the predicate that we actually
     care about when considering the Nest machine
  3. Most importantly, the theorem is hard to prove because because there's alot of book
     keeping involved in ensuring that each predicate is in the "same place" of the
     inductive structure. That is, when we apply inversion with a given chart
     structure it has to be done with both predicates and then the variables
     have to be lined up. Normally this happens as `inversion H1; inversion H2; subst`
     but it is frequently the case there are unification issues when later employing
     the facts generated by the inversion with the inductive hypothesis.

  Instead, where we are concerned with one level of the chart at a time we might like
  to pattern match on the context and then say what is to be proved for each. This
  is the approach taken in the `qspec_must_go_fix` theorem below.

  The downside is that when one is defining a predicate which is pattern matching
  on the inductive structure we must remember to include the inductive case. This
  is also true when defining the predicates as inductive structures (as in the example)
  above but there it's very easy to copy and paste the original inductive definition
  of something like chart_step and then modify it with the predicate.

  Alternately we might merge both approachs, copying and pasting the inductive structure
  of `chart_step` and then adding an additional arguement predicate over the chart
  the configurations and the enivronments. This is the approach taken in the `qspec_must_go_ind`
  theorem below.

  The downside is that we are copying the inductive structure everywhere.

  Both seem to require about the same level of proof effort.
 *)

Definition Pred := (Chart -> Config -> Env -> Config -> Env -> Type).

Inductive chart_step_pred : Pred -> Chart -> (Config * E) -> (Config * E) -> Prop :=
| CSP_Unit : forall Pr env env',
    Pr Unit U env U env' ->
    chart_step_pred Pr Unit (U, env) (U, env')
| CSP_Par : forall Pr ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env',
    Pr (Par ch1 ch2) (P cfg1 cfg2) env (P cfg1' cfg2') env' ->
    chart_step_pred Pr ch1 (cfg1, env) (cfg1', env') ->
    chart_step_pred Pr ch2 (cfg2, env) (cfg2', env') ->
    chart_step_pred Pr (Par ch1 ch2) (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CSP_Nest_Outer : forall Pr m cs x cfg env x' cfg' env',
    Pr (Nest m cs) (Config.N x cfg) env (Config.N x' cfg') env' ->
    machine_step m (x, env) (x', env') ->
    chart_terminal (cs x) (cfg, env) ->
    chart_initial (cs x') (cfg', env') ->
    chart_step_pred Pr (Nest m cs) (N x cfg, env) (N x' cfg', env')
| CSP_Nest_Inner : forall Pr m cs x x' cfg env cfg' env',
    Pr (Nest m cs) (Config.N x cfg) env (Config.N x cfg') env' ->
    machine_inner m x env env' ->
    chart_step_pred Pr (cs x) (cfg, env) (cfg', env') ->
    chart_step_pred Pr (Nest m cs) (Config.N x cfg, env) (Config.N x' cfg', env').

Definition must_go_pred c cfg1 env1 cfg2 env2 :=
    match (c, cfg1, cfg2) with
    | ((Nest m cs), (Config.N x cfg), (Config.N x' cfg')) =>
      if Nat.eq_dec x x'
      then True
      else (machine_step m (x, env1) (x', env2) -> ~ machine_inner m x env1 env2)
    | _ => True
    end.

Theorem qspec_must_go_ind :
  forall qchart qspec data cfg1 cfg2 env1 env2,
    qchart = semantics qspec data
    -> chart_step qchart (cfg1, env1) (cfg2, env2)
    -> chart_step_pred must_go_pred qchart (cfg1, env1) (cfg2, env2).
Proof.
  intro qchart.
  induction qchart; intros; (edestruct chart_step_config; eauto); do 2 force_config;
    [constructor | constructor | ];
    try match goal with
    | _ : _ |- must_go_pred _ _ _ _ _ => unfold must_go_pred; auto
        end.

  inversion H0.
  edestruct par_child_semantics as ((? & ?) & (? & ?)). eauto.
  eapply IHqchart1; eauto.

  inversion H0.
  edestruct par_child_semantics as ((? & ?) & (? & ?)). eauto.
  eapply IHqchart2; eauto.

  inversion H1.
  apply CSP_Nest_Outer; auto.
  unfold must_go_pred; simpl.
  destruct Nat.eq_dec; auto.
  eapply qspec_base_must_go; eauto.

  apply CSP_Nest_Inner; auto.
  unfold must_go_pred; simpl.
  destruct Nat.eq_dec; auto.

  edestruct nest_child_semantics. eauto.
  eauto.
Qed.

Fixpoint must_go c cfg1 env1 cfg2 env2 :=
    match (c, cfg1, cfg2) with
    | (Unit, _, _) => True
    | ((Nest m cs), (Config.N x cfg), (Config.N x' cfg')) =>
      (forall s, chart_step (cs s) (cfg, env1) (cfg', env2) -> must_go (cs s) cfg env1 cfg' env2) /\
      (machine_step m (x, env1) (x', env2) -> ~ machine_inner m x env1 env2)
    | ((Par ch1 ch2), (P cfg1 cfg2), (P cfg1' cfg2')) =>
      (must_go ch1 cfg1 env1 cfg1' env2) /\
      (must_go ch2 cfg2 env1 cfg2' env2)
    | _ => False
    end.

Theorem qspec_must_go_fix :
  forall qchart qspec data cfg1 cfg2 env1 env2,
    qchart = semantics qspec data
    -> chart_step qchart (cfg1, env1) (cfg2, env2)
    -> must_go qchart cfg1 env1 cfg2 env2.
Proof.
  intro qchart.
  induction qchart; intros; (edestruct chart_step_config; eauto);
  do 2 force_config;
  match goal with
  | _ : _ |- must_go _ _ _ _ _ => unfold must_go; auto
  end;
  fold must_go.
  - split;
      edestruct par_child_semantics as ((? & ?) & (? & ?)); eauto;
      inversion H0;
      [ eapply IHqchart1
      | eapply IHqchart2 ];
      eauto.
  - split.
    + intros.
      edestruct nest_child_semantics; eauto.
    + eapply qspec_base_must_go; eauto.
Qed.

(* NOTE we just want to identify when there is any inner step enabled
   whether or not that step might not be taken for other reasons. For example
   in our syncrhonous semantics the parallel machines must step together
   even if one has an enabled inner step
 *)
Inductive chart_machine_inner_step : Chart -> Chart -> (Config * E) -> (Config * E) -> Prop :=
| CMIS_Unit : forall env env',
    chart_machine_inner_step Unit Unit (U, env) (U, env')
| CMIS_Par_Left : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env' nest,
    chart_machine_inner_step ch1 nest (cfg1, env) (cfg1', env') ->
    chart_machine_inner_step (Par ch1 ch2) nest (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CMIS_Par_Right : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env' nest,
    chart_machine_inner_step ch2 nest (cfg2, env) (cfg2', env') ->
    chart_machine_inner_step (Par ch1 ch2) nest (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CMIS_Nest : forall m cs x cfg env cfg' env',
    machine_inner m x env env' ->
    chart_machine_inner_step (Nest m cs) (Nest m cs) (Config.N x cfg, env) (Config.N x cfg', env')
| CMIS_Nest_Ind : forall m cs x cfg env cfg' env' nest,
    chart_machine_inner_step (cs x) nest (cfg, env) (cfg', env') ->
    chart_machine_inner_step (Nest m cs) nest (Config.N x cfg, env) (Config.N x cfg', env').

Inductive chart_machine_step : Chart -> Chart -> (Config * E) -> (Config * E) -> Prop :=
| CMS_Unit : forall env env',
    chart_machine_step Unit Unit (U, env) (U, env')
| CMS_Par_Left : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env' nest,
    chart_machine_step ch1 nest (cfg1, env) (cfg1', env') ->
    chart_machine_step (Par ch1 ch2) nest (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CMS_Par_Right : forall ch1 cfg1 cfg1' ch2 cfg2 cfg2' env env' nest,
    chart_machine_step ch2 nest (cfg2, env) (cfg2', env') ->
    chart_machine_step (Par ch1 ch2) nest (P cfg1 cfg2, env) (P cfg1' cfg2', env')
| CMS_Nest : forall m cs x x' cfg env cfg' env',
    machine_step m (x, env) (x', env') ->
    chart_machine_step (Nest m cs) (Nest m cs) (Config.N x cfg, env) (Config.N x' cfg', env')
| CMS_Nest_Ind : forall m cs x cfg env cfg' env' nest,
    chart_machine_step (cs x) nest (cfg, env) (cfg', env') ->
    chart_machine_step (Nest m cs) nest (Config.N x cfg, env) (Config.N x cfg', env').

(* NOTE it's possible that (Nest m cs) exists at many levels in a chart but then
   the definitions of `machine_step` and `machine_inner` are the same and we expect
   that they should adhear to the same properties based on the environment anyway

   NOTE keeping for posterity and comparison with the inductive predicate approach
 *)
Theorem qspec_must_go :
  forall qchart qspec data m cs cfg1 cfg2 env1 env2,
    qchart = semantics qspec data
    -> chart_machine_step qchart (Nest m cs) (cfg1, env1) (cfg2, env2)
    -> ~ chart_machine_inner_step qchart (Nest m cs) (cfg1, env1) (cfg2, env2).
Abort.
