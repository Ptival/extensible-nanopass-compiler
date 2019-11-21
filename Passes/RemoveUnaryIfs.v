(* From Coq Require Import Logic.FunctionalExtensionality. *)

From BlueSky Require Import Algebra.
From BlueSky Require Import Eval.
From BlueSky Require Import Functor.
From BlueSky Require Import ProgramAlgebra.
From BlueSky Require Import ProofAlgebra.
From BlueSky Require Import SubFunctor.
From BlueSky Require Import Sum1.
From BlueSky Require Import UniversalProperty.

From BlueSky.Features Require Import Bool.
From BlueSky.Features Require Import If1.
From BlueSky.Features Require Import If2.
From BlueSky.Features Require Import Stuck.
From BlueSky.Features Require Import Unit.

Local Open Scope Sum1_scope.
Local Open Scope SubFunctor_scope.

Definition
  wrongRemoveUnaryIfsAlgebra
  {O} `{Functor O} `{FunctorLaws O}
  `{O supports UnitF}
  `{O supports If2F}
  T
  : ProgramAlgebra If1F T (Fix O)
  :=
    {|
      programAlgebra :=
        fun rec '(If1 c t) =>
          proj1_sig unit;
    |}.

Definition
      removeUnaryIfsAlgebra'
      {O} `{Functor O} `{FunctorLaws O}
      `{O supports UnitF}
      `{O supports If2F}
      (T : Set)
      (rec : T -> WellFormedValue O)
      '(If1 condition thenBranch)
  : WellFormedValue O
  :=
    if2
      (rec condition)
      (rec thenBranch)
      unit.

Global Instance
       removeUnaryIfsAlgebra
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports UnitF}
       `{O supports If2F}
       T
  : ProgramAlgebra If1F T (WellFormedValue O)
  :=
    {|
      programAlgebra := removeUnaryIfsAlgebra' T;
    |}.

Set Typeclasses Debug.

Definition
      removeUnaryIfs
      {L O} `{Functor L} `{Functor O} `{FunctorLaws L} `{FunctorLaws O}
      `{O supports UnitF}
      `{O supports If2F}
  : Fix (If1F + L) -> Fix O
  := mendlerFold programAlgebra.

(* Definition *)
(*       removeUnaryIfs *)
(*       {L O} `{Functor L} `{Functor O} `{FunctorLaws O} *)
(*       `{O supports UnitF} *)
(*       `{O supports If2F} *)
(*       `{Eval L O} *)
(*   : Fix (If1F + L) -> Fix O *)
(*   := mendlerFold programAlgebra. *)

Theorem testing
        {L O} `{Functor L} `{Functor O}
        `{L supports If1F}
        `{O supports UnitF}
        `{O supports If2F}
        `{Eval L O}
  : forall (e : Fix (If1F + L)) A rec,
    mendlerFold evalAlgebra e A rec
    =
    mendlerFold evalAlgebra (removeUnaryIfs e) A rec.
Proof.
  unfold removeUnaryIfs.
  unfold evalAlgebra.
  compute.
  f_equal.
  destruct H6.
  Set Printing All.
  idtac.
  compute.
  destruct e.
  unfold evalAlgebra.
Qed.
