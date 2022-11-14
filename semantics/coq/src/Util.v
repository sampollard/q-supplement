Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

Section Prefix.

  Variable A : Type.

  Inductive prefix : list A -> list A -> Prop :=
  | prefix_empty : forall l, prefix [] l
  | prefix_cons : forall x l l', prefix l l' -> prefix (x::l) (x::l').

  Lemma prefix_refl :
    forall l, prefix l l.
  Proof.
    induction l; constructor; assumption.
  Qed.

  Lemma prefix_app :
    forall l1 l2 l3, prefix l1 l2 -> prefix l1 (l2 ++ l3).
  Proof.
    intros l1 l2 l3 Hpre.
    induction Hpre; simpl; constructor; assumption.
  Qed.

  Lemma prefix_app_exists :
    forall l1 l3, prefix l1 l3 -> exists l2, l3 = l1 ++ l2.
  Proof.
    intros l1 l2 Hpre.
    induction Hpre.
    exists l; reflexivity.
    inversion IHHpre as [l2 Hl2].
    rewrite Hl2.
    exists l2.
    reflexivity.
  Qed.

End Prefix.


Section Postfix.

  Variable A : Type.

  Inductive postfix (l : list A) : list A -> Prop :=
  | postfix_refl : postfix l l
  | postfix_cons : forall x l', postfix l l' -> postfix l (x::l').

  Lemma postfix_empty :
    forall l, postfix [] l.
  Proof.
    induction l; constructor; assumption.
  Qed.

  Lemma postfix_app :
    forall l1 l2 l3, postfix l1 l2 -> postfix (l1 ++ l3) (l2 ++ l3).
  Proof.
    intros l1 l2 l3 Hpost.
    induction Hpost; simpl; constructor; assumption.
  Qed.

  Lemma postfix_app_exists :
    forall l1 l3, postfix l1 l3 -> exists l2, l3 = l2 ++ l1.
  Proof.
    intros l1 l3 Hpost.
    induction Hpost.
    exists []; reflexivity.
    rename l' into l3.
    inversion IHHpost as [l2 Hl2].
    exists (x::l2); simpl.
    rewrite Hl2; reflexivity.
  Qed.

  Theorem prefix_postfix_rev :
    forall l1 l2, prefix l1 l2 -> postfix (rev l1) (rev l2).
  Proof.
    intros l1 l2 Hpre.
    induction Hpre.
    apply postfix_empty.
    apply postfix_app.
    assumption.
  Qed.

  Theorem postfix_prefix_rev :
    forall l1 l2, postfix l1 l2 -> prefix (rev l1) (rev l2).
  Proof.
    intros l1 l2 Hpost.
    induction Hpost.
    apply prefix_refl.
    apply prefix_app.
    assumption.
  Qed.

End Postfix.

Section Assoc.

  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.
  Variable B : Type.

  Fixpoint assoc (l : list (A*B)) (x : A) : option B :=
    match l with
    | [] => None
    | ab::l' => let '(a,b) := ab in if eq_dec x a then Some b else assoc l' x
    end.

End Assoc.

Section FunctionDef.

  Variable A B : Type.
  Variable R : A -> B -> Prop.

  Definition function := forall a, exists! b, R a b.

  Theorem function_eq :
    function ->
    forall a b b', R a b -> R a b' -> b' = b.
  Proof.
    unfold function.
    intros H a b b' Hb Hb'.
    specialize (H a).
    inversion H as [b'' Huniq].
    replace b with b'' by (apply Huniq; assumption).
    replace b' with b'' by (apply Huniq; assumption).
    reflexivity.
  Qed.

End FunctionDef.

Section ListRel.

  Variable A B : Type.
  Variable R : A -> B -> Prop.

  Inductive list_rel : list A -> list B -> Prop :=
  | list_rel_nil : list_rel [] []
  | list_rel_cons : forall x xs y ys,
      list_rel xs ys -> R x y -> list_rel (x::xs) (y::ys).

  Theorem function_rel__function_list_rel :
    function R -> function list_rel.
  Proof.
    unfold function.
    intros Hf xs.
    induction xs as [|x xs].

    (* Nil *)
    exists [].
    split.
    constructor.
    intros ys Hlr.
    inversion Hlr.
    reflexivity.

    (* Cons *)
    inversion IHxs as [ys Hys]; subst; clear IHxs.
    specialize (Hf x).
    inversion Hf as [y Hy]; subst; clear Hf.
    exists (y::ys).
    destruct Hys as [Hlrs Hys_uniq].
    destruct Hy as [HRxy Hy_uniq].
    split.
    constructor; assumption.
    intros ys'.
    destruct ys' as [|y' ys']; intros H; inversion H; subst; clear H.
    replace y' with y by (apply Hy_uniq; assumption).
    replace ys' with ys by (apply Hys_uniq; assumption).
    reflexivity.
  Qed.

  Theorem function_list_rel__function_rel :
    function list_rel -> function R.
  Proof.
    unfold function.
    intros H a.
    specialize (H [a]).
    inversion H as [bs (Hb,Huniq)].
    destruct bs; inversion Hb; subst; clear Hb.
    exists b.
    split.
    assumption.
    intros b' Hb'.
    inversion H3; subst; clear H3.
    assert (list_rel [a] [b']) as Hlb'.
    constructor.
    constructor.
    assumption.
    specialize (Huniq [b'] Hlb').
    inversion Huniq.
    reflexivity.
  Qed.

End ListRel.


Section ListRelEq.

  Variable A : Type.

  Theorem list_rel_eq__list_eq :
    forall (l1 l2 : list A), list_rel eq l1 l2 -> l1 = l2.
  Proof.
    induction l1; intros l2 Hlr;
      inversion Hlr as [ | x xs y ys]; subst.
    reflexivity.
    replace ys with l1 by (apply IHl1; assumption); reflexivity.
  Qed.

End ListRelEq.


Section FunctionComposition.

  Variable A B C : Type.

  Definition comp (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : A -> C -> Prop :=
    fun a c => forall b, R1 a b -> R2 b c.

  Theorem comp_function :
    forall R1 R2,
      function R1 -> function R2 -> function (comp R1 R2).
  Proof.
    unfold function, comp.
    intros R1 R2 HR1 HR2 a.
    specialize (HR1 a).
    inversion HR1 as [b (Hb,Hb1)]; clear HR1.
    specialize (HR2 b).
    inversion HR2 as [c (Hc,Hc1)]; clear HR2.
    exists c.
    split.
    intros b' Hb'.
    replace b'  with b by (apply Hb1; assumption).
    assumption.
    intros c' Hc'.
    apply Hc1.
    apply Hc'.
    assumption.
  Qed.

  Theorem comp_correct :
    forall (f : B -> C) (g : A -> B) x y,
      f (g x) = y <-> comp (fun a b => g a = b) (fun b c => f b = c) x y.
  Proof.
    unfold comp.
    intros f g x y.
    split; intros H.
    intros b Hg; subst; reflexivity.
    apply H.
    reflexivity.
  Qed.

End FunctionComposition.


Section Relations.

  Section Converse.
    Variable A B : Type.
    Variable R : A -> B -> Prop.

    Definition transp (b : B) (a : A) : Prop := R a b.
  End Converse.

End Relations.
