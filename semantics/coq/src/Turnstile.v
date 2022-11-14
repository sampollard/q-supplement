Require Import Chart.Util.
Require Import Chart.Semantics.Config.
Require Import Chart.Semantics.ConfigEnv.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Set Implicit Arguments.

Module Config <: ConfigType.
  Definition S := string.
  Definition E := unit.
  Inductive Config :=
  | U : Config
  | P : Config -> Config -> Config
  | N : S -> Config -> Config.
End Config.
Import Config.

Module CfgEnv := ConfigEnvSemantics Config.
Import CfgEnv.

Section Syntax.
  Definition nest m cs : Chart :=
    Nest m (fun x => match assoc string_dec cs x with
                     | Some ch => ch
                     | None => Unit
                     end).
End Syntax.


Section Turnstile.

  Definition power :=
    {| machine_initial '(x, tt) := In x ["Off"];
       machine_terminal '(x, tt) := In x [];
       machine_inner x tt tt := In x ["Off"; "On"];
       machine_step '(x,tt) '(x',tt) := In (x, x') [("Off", "On"); ("On", "Off")]
    |}.

  Definition gate :=
    {| machine_initial '(x, tt) := In x ["Locked"];
       machine_terminal '(x, tt) := In x ["Locked"; "Unlocked"];
       machine_inner x tt tt := In x ["Locked"; "Unlocked"];
       machine_step '(x,tt) '(x',tt) := In (x, x') [("Locked", "Unlocked"); ("Unlocked", "Locked")]
    |}.

  Definition card :=
    {| machine_initial '(x, tt) := In x ["Ready"];
       machine_terminal '(x, tt) := In x ["Ready"; "Reading"; "Accept"];
       machine_inner x tt tt := In x ["Ready"; "Reading"; "Accept"];
       machine_step '(x, tt) '(x', tt) :=
         In (x, x') [ ("Ready", "Reading");
                      ("Reading", "Ready");
                      ("Reading", "Accept");
                      ("Accept", "Ready")
                    ]
    |}.

  Definition turnstile := nest power [("On", Par (nest gate []) (nest card []))].

  Goal chart_initial turnstile (N "Off" U, tt).
  Proof.
    apply CI_Nest.
    simpl.
    intuition.
    simpl.
    apply CI_Unit.
  Qed.

  Goal chart_step turnstile
       (N "Off" U, tt)
       (N "On" (P (N "Locked" U) (N "Ready" U)), tt).
  Proof.
    repeat constructor.
  Qed.

  Goal chart_refines (nest power []) turnstile.
    unfold turnstile.
    constructor.
    intros x.
    destruct (string_dec x "On") as [H | H]; constructor.
  Qed.
End Turnstile.
