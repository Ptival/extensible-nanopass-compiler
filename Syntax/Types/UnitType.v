From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

From ExtensibleCompiler.Syntax.Terms Require Import Unit.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

Inductive UnitType (A : Set) : Set :=
| MkUnitType : UnitType A
.
Arguments MkUnitType {A}.

Global Instance Functor_UnitType
  : Functor UnitType
  :=
    {|
      fmap := fun A B f 'MkUnitType => MkUnitType;
    |}.

Global Instance FunctorLaws_UnitType
  : FunctorLaws UnitType.
Proof.
  apply Build_FunctorLaws.
  {
    move => ? [] //.
  }
  {
    move => ????? [] //.
  }
Qed.

Definition unitType'
           {LT} `{FunctorLaws LT} `{SubFunctor UnitType LT}
  : TypeFix LT
  := injectUniversalProperty MkUnitType.

Definition unitType
           {LT} `{FunctorLaws LT} `{SubFunctor UnitType LT}
  : Fix LT
  := proj1_sig unitType'.

Global Instance ReverseFoldUniversalProperty_unitType
           {LT} `{FunctorLaws LT} `{SubFunctor UnitType LT}
  : ReverseFoldUniversalProperty unitType
  := proj2_sig unitType'.

Definition isUnitType
           {LT} `{FunctorLaws LT} `{SubFunctor UnitType LT}
  : Fix LT -> bool
  := fun typ =>
       match project typ with
       | Some MkUnitType => true
       | None            => false
       end.

Definition typeEquality_UnitType
           DT `{FunctorLaws DT} `{SubFunctor UnitType DT}
           (R : Set) (rec : R -> TypeEqualityResult DT) (e : UnitType R)
  : TypeEqualityResult DT
  :=
    match e with
    | MkUnitType => fun t => isUnitType (proj1_sig t)
    end.

Global Instance TypeEquality_UnitType
       DT `{FunctorLaws DT} `{SubFunctor UnitType DT}
       T
  : ProgramAlgebra UnitType T (TypeEqualityResult DT)
  := {| programAlgebra := typeEquality_UnitType DT T|}.
