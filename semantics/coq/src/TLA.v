Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Set Implicit Arguments.

Section Base.

  Variable Var : Set.
  Variable Val : Set.

  Definition State := Var -> Val.
  Definition StateFunc := State -> Val.
  Definition Predicate := State -> Prop.
  Definition Action := State -> State -> Prop.

  Definition unchanged (f : StateFunc) : Action :=
    fun st st' => f st = f st'.

  Definition pred (P : Predicate) : Action :=
    fun st st' => P st.

  Definition prime (P : Predicate) : Action :=
    fun st st' => P st'.

  Inductive Formula :=
  | F_Act : Action -> Formula
  | F_Enabled : Action -> Formula
  | F_Always : Formula -> Formula
  | F_Eventually : Formula -> Formula
  | F_Not : Formula -> Formula
  | F_And : Formula -> Formula -> Formula
  | F_Or : Formula -> Formula -> Formula
  | F_Imp : Formula -> Formula -> Formula
  | F_Iff : Formula -> Formula -> Formula.

  Definition Trace := nat -> State.
  Definition shift (t : Trace) (n : nat) : Trace := fun m => t (n + m).
  Infix "<<" := shift (at level 55, left associativity).

  Section Shift.
    Variable t : Trace.
    (* Make sure we got the precedence and associativity right. *)
    (* Check (t << 10 << 5 + 1 << 2 * 10 << 10 - 9). *)

    Theorem shift_id :
      t << 0 = t.
    Proof.
      reflexivity.
    Qed.

    Theorem shift_add :
      forall n m, t << n << m = t << n + m.
    Proof.
      unfold shift.
      intros n m.
      apply functional_extensionality.
      intros x.
      f_equal.
      apply Nat.add_assoc.
    Qed.

    Theorem shift_app :
      forall n i, (t << n) i = t (n + i).
    Proof.
      intros n i.
      unfold shift.
      reflexivity.
    Qed.

    Lemma shift_app_add :
      forall i j k, (t << i + j) k = (t << i) (j + k).
    Proof.
      intros i j k.
      repeat (rewrite shift_app).
      intuition.
    Qed.

  End Shift.

  Fixpoint satisfies (fm : Formula) (t : Trace) : Prop :=
    match fm with
    | F_Act A => A (t 0) (t 1)
    | F_Enabled A => exists st', A (t 0) st'
    | F_Always p => forall n, satisfies p (t << n)
    | F_Eventually p => exists n, satisfies p (t << n)
    | F_Not p => ~satisfies p t
    | F_And p q => satisfies p t /\ satisfies q t
    | F_Or p q => satisfies p t \/ satisfies q t
    | F_Imp p q => satisfies p t -> satisfies q t
    | F_Iff p q => satisfies p t <-> satisfies q t
    end.

  Notation "~ A" := (F_Not A) : tla_scope.
  Infix "/\" := F_And : tla_scope.
  Infix "\/" := F_Or : tla_scope.
  Infix "==>" := F_Imp (at level 99, right associativity) : tla_scope.
  Infix "<==>" := F_Iff (at level 95, no associativity) : tla_scope.
  Notation "[] F" := (F_Always F) (at level 75, right associativity) : tla_scope.
  Notation "<> F" := (F_Eventually F) (at level 75, right associativity) : tla_scope.

  Delimit Scope tla_scope with tla.

  Definition F_Pred (P : Predicate) : Formula :=
    F_Act (pred P).

  Definition F_Box (A : Action) (f : StateFunc) : Formula :=
    F_Or (F_Act A) (F_Act (unchanged f)).

  Coercion F_Act : Action >-> Formula.
  Coercion F_Pred : Predicate >-> Formula.

  Local Open Scope tla_scope.

  Definition valid (fm : Formula) := forall t, satisfies fm t.

  Theorem STL2 :
    forall F, valid ([]F ==> F).
  Proof.
    intros F t; simpl.
    intros H.
    specialize H with 0.
    assumption.
  Qed.

  Theorem STL3 :
    forall F, valid ([][]F <==> []F).
  Proof.
    intros F t; simpl.
    split; intros H.

    intros n.
    specialize (H n 0).
    assumption.

    intros n m.
    specialize H with (n + m).
    rewrite shift_add.
    assumption.
  Qed.

  Theorem STL4 :
    forall F G, valid (F ==> G) -> valid ([]F ==> []G).
  Proof.
    intros F G.
    unfold valid; simpl.
    intuition.
  Qed.

  Theorem STL5 :
    forall F G,
      valid ( [](F /\ G) <==> []F /\ []G).
  Proof.
    intros F G.
    unfold valid; simpl.
    split; [intros H; split; intros n; specialize (H n) | idtac]; intuition.
  Qed.

  Theorem TLA1 :
    forall (P : Predicate) f,
      valid (P /\ unchanged f ==> prime P) ->
      valid ([]P <==> P /\ []((P ==> prime P) \/ unchanged f)).
  Proof.
    intros P f.
    unfold valid, unchanged; simpl.
    unfold pred, prime; simpl.
    intros H t; split.

    intros Hn; split.
    specialize Hn with 0; assumption.

    left; intros.
    specialize Hn with (n+1).
    rewrite shift_app_add in Hn.
    assumption.

    intros (HP, Hn).
    induction n; try assumption.
    replace (S n) with (n+1) by apply Nat.add_1_r.
    rewrite shift_app_add.
    specialize H with (t << n).
    specialize Hn with n.
    intuition.
  Qed.

  Theorem TLA2 :
    forall (P Q : Predicate) (A B : Action) (f g : StateFunc),
      valid (P /\ (F_Box A f) ==> Q /\ (F_Box B g)) ->
      valid ([]P /\ [](F_Box A f) ==> []Q /\ [](F_Box B g)).
  Proof.
    intros P Q A B f g.
    unfold valid, unchanged; simpl.
    unfold pred; simpl.
    intros Ht t (HP, HA).
    split;
      intros n;
      specialize Ht with (t << n);
      specialize HP with n;
      specialize HA with n;
      intuition.
  Qed.

  Theorem INV1 :
    forall (I : Predicate) (N : Action) (f : StateFunc),
      valid (I /\ (F_Box N f) ==> prime I) ->
      valid (I /\ [](F_Box N f) ==> []I).
  Proof.
    intros I N f.
    unfold valid, unchanged; simpl.
    unfold pred, prime; simpl.
    intros Ht t.
    intros (H0, Hn) n.
    induction n; try assumption.
    replace (S n) with (n+1) by apply Nat.add_1_r.
    rewrite shift_app_add.
    specialize Hn with n.
    intuition.
  Qed.

End Base.
