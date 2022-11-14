Require Import Coq.Lists.List.
Require Import Chart.Util.
Set Implicit Arguments.
Import ListNotations.

Section Process.

  Variable A : Type.

  Record Process := process
    {
      initial : A -> Prop;
      step : A -> A -> Prop
    }.

  Variable m : Process.

  Inductive reachable : A -> Prop :=
  | reachable_initial : forall x,
      initial m x -> reachable x
  | reachable_step : forall x y,
      reachable x -> step m x y -> reachable y.

  Definition deterministic :=
    (forall x x', initial m x -> initial m x' -> x = x') /\
    (forall x, reachable x -> forall y y', step m x y -> step m x y' -> y = y').

  Definition reactive :=
    forall x, reachable x -> exists y, step m x y.

  Definition stuttering :=
    forall x, reachable x -> step m x x.

  Lemma reactive_reachable :
    reactive ->
    forall x, reachable x -> exists x', reachable x'.
  Proof.
    unfold reactive.
    intros Hreact x Hreach.
    specialize (Hreact x Hreach).
    inversion Hreact as (y,Hy).
    exists y.
    apply reachable_step with x; assumption.
  Qed.

  Inductive trace_to : A -> list A -> Prop :=
  | trace_to_initial : forall x,
      initial m x -> trace_to x []
  | trace_to_step : forall x x' t,
      trace_to x t -> step m x x' -> trace_to x' (x::t).

  Definition trace (t : list A) :=
    match t with
    | [] => True
    | (x::t') => trace_to x t'
    end.

  Lemma initial_trace :
    forall x, trace [x] -> initial m x.
  Proof.
    intros x Ht.
    inversion Ht.
    assumption.
  Qed.

  Lemma step_trace :
    forall x y t, trace (y::x::t) -> step m x y.
  Proof.
    intros x y t Ht.
    inversion Ht; subst.
    assumption.
  Qed.

  Theorem reachable_trace :
    forall x, reachable x -> exists t, trace (x::t).
  Proof.
    unfold trace.
    intros x Hreach.
    induction Hreach.
    exists []; constructor; assumption.
    inversion IHHreach as (t,Ht).
    exists (x::t).
    apply trace_to_step; assumption.
  Qed.

  Lemma trace_reachable :
    forall x t, trace (x::t) -> reachable x.
  Proof.
    unfold trace.
    intros x t Htrace.
    induction Htrace.
    constructor; assumption.
    apply reachable_step with x; assumption.
  Qed.

  Lemma trace_cons :
    forall x t, trace (x::t) -> trace t.
  Proof.
    intros x t Ht.
    destruct Ht.
    simpl; constructor.
    assumption.
  Qed.

  Theorem in_trace_reachable :
    forall t x, trace t -> In x t -> reachable x.
  Proof.
    intros t x Ht H.
    induction t; inversion H; subst.
    eauto using trace_reachable.
    apply IHt; eauto using trace_cons.
  Qed.

  Lemma trace_app :
    forall t1 t2, trace (t1++t2) -> trace t2.
  Proof.
    intros t1 t2 H.
    induction t1 as [|x t1].
    assumption.
    apply IHt1.
    simpl in H.
    apply trace_cons with x.
    assumption.
  Qed.

  Theorem trace_postfix :
    forall t1 t2, postfix t1 t2 -> trace t2 -> trace t1.
  Proof.
    intros t1 t2 Hpost Ht2.
    induction Hpost.
    assumption.
    apply IHHpost.
    apply trace_cons with x.
    assumption.
  Qed.

  Definition invariant (P : A -> Prop) :=
    forall x, reachable x -> P x.

  Definition trace_property (P : list A -> Prop) :=
    forall t, trace t -> P t.

  Theorem invariant_trace_property :
    forall P, invariant P <-> trace_property (Forall P).
  Proof.
    unfold invariant, trace_property.
    split; intros H.

    intros t Ht.
    apply Forall_forall.
    intros x Hx.
    apply H.
    apply in_trace_reachable with t; assumption.

    intros x Hx.
    apply reachable_trace in Hx.
    inversion Hx as [t Ht].
    specialize (H (x::t) Ht).
    rewrite Forall_forall in H.
    apply H.
    apply in_eq.
  Qed.

  Theorem unreachable_invariant :
    forall x, ~(reachable x) <-> invariant (fun st => st <> x).
  Proof.
    unfold invariant, not.
    split; intro H; intros; subst;
      eapply H; eauto.
  Qed.

End Process.


Section Safety.

  Variable A : Type.

  Definition safety (P : list A -> Prop) :=
    forall l1 l2, P l2 -> postfix l1 l2 -> P l1.

  Theorem trace_safety :
    forall (m : Process A), safety (trace m).
  Proof.
    unfold safety.
    eauto using trace_postfix.
  Qed.

End Safety.


Section Refinement.

  Variable A : Type.           (* "Abstract" states *)
  Variable C : Type.           (* "Concrete" states *)
  Variable ma : Process A.     (* Abstract machine *)
  Variable mc : Process C.     (* Concrete machine *)
  Variable R : C -> A -> Prop. (* State relation *)

  Definition refinement :=
    forall tc, trace mc tc -> exists ta, list_rel R tc ta /\ trace ma ta.

  Section RefinementProperties.

    (* It would be nice if our definitions allowed us to derive that R
    must be a function or Galois connection or whatever.  In fact, at
    least for the properties below, we don't seem to need unique
    existance, merely existance. *)
    (* Hypothesis R_func : function R. *)
    Hypothesis Href : refinement.

    Lemma refinement_reachable :
      forall c, reachable mc c -> exists a, R c a /\ reachable ma a.
    Proof.
      intros c Hc.
      apply reachable_trace in Hc.
      inversion Hc as [tc Htc]; subst; clear Hc.
      specialize (Href (c::tc) Htc).
      inversion Href as (ta, (HR,Hta)); subst; clear Href.
      destruct ta as [|a ta].
      inversion HR.
      exists a.
      split.
      inversion HR; subst; clear HR; assumption.
      apply trace_reachable with ta; assumption.
    Qed.

    Theorem refinement_trace_property :
      forall (Pa : list A -> Prop) (Pc : list C -> Prop),
        (forall ta tc, list_rel R tc ta -> Pa ta -> Pc tc) ->
        trace_property ma Pa ->
        trace_property mc Pc.
    Proof.
      unfold trace_property.
      unfold refinement in Href.
      intros Pa Pc HP Ha tc Htc.
      specialize (Href tc Htc).
      inversion Href as (ta, (HR,Hta)).
      specialize (HP ta tc HR).
      apply HP.
      apply Ha.
      assumption.
    Qed.

    Theorem refinement_invariant :
      forall (Ia : A -> Prop) (Ic : C -> Prop),
        (forall c a, R c a -> Ia a -> Ic c) ->
        invariant ma Ia ->
        invariant mc Ic.
    Proof.
      intros Ia Ic.
      repeat (rewrite invariant_trace_property).
      intros H.
      apply refinement_trace_property.
      intros tc ta HRl.

      induction HRl as [| c tc a ta HRl Hi HR].
      intros; constructor.
      specialize (H c a HR).
      intros Ha.
      inversion Ha; subst; clear Ha.
      constructor; auto.
    Qed.

  End RefinementProperties.

  Section Simulation.

    Definition simulation :=
      (forall c, initial mc c -> exists a, R c a /\ initial ma a) /\
      (forall c c' a, step mc c c' -> R c a -> exists a', R c' a' /\ step ma a a').

    Theorem simulation_refinement :
      simulation -> refinement.
    Proof.
      unfold simulation, refinement.
      intros (Hinit,Hstep) tc Htc.

      destruct tc as [| c tc].
      exists [].
      split; constructor.

      induction Htc.

      rename x into c.
      specialize (Hinit c H).
      inversion Hinit as (a,(HR,Ha)).
      exists [a].
      split; repeat constructor; auto.

      rename x into c.
      rename x' into c'.
      rename t into tc.
      inversion IHHtc as (ta, (HR, Hta)); clear IHHtc.
      inversion HR; subst; clear HR.
      rename y into a.
      rename ys into ta.
      rename H into Hsc.
      rename H4 into HR.
      specialize (Hstep c c' a Hsc HR).
      inversion Hstep as (a', (HR',Ha)); clear Hstep.
      exists (a'::a::ta).
      split; repeat constructor; auto.
    Qed.

  End Simulation.

End Refinement.


Section BiRefinement.

  Variable A : Type.
  Variable B : Type.
  Variable ma : Process A.
  Variable mb : Process B.
  Variable R : A -> B -> Prop.

  Definition birefinement :=
    refinement ma mb (transp R) /\ refinement mb ma R.

End BiRefinement.
