From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

From ExtensibleCompiler.Features Require Import Types.

Local Open Scope SubFunctor_scope.

Inductive BoolType (A : Set) : Set :=
| MkBoolType : BoolType A
.
Arguments MkBoolType {A}.

Global Instance Functor_BoolType
  : Functor BoolType
  := {| fmap := fun A B f 'MkBoolType => MkBoolType; |}.

Global Instance FunctorLaws_BoolType
  : FunctorLaws BoolType.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition boolType'
           {LT} `{FunctorLaws LT} `{BoolType <= LT}
  : TypeFix LT
  := injectUniversalProperty MkBoolType.

Definition boolType
           {LT} `{FunctorLaws LT} `{BoolType <= LT}
  : Fix LT
  := proj1_sig boolType'.

Global Instance ReverseFoldUniversalProperty_boolType
           LT `{FunctorLaws LT} `{BoolType <= LT}
  : ReverseFoldUniversalProperty boolType
  := proj2_sig boolType'.

Definition isBoolType
           {LT} `{FunctorLaws LT} `{S : BoolType <= LT}
  : Fix LT -> bool
  := fun typ =>
       match project typ with
       | Some MkBoolType => true
       | None            => false
       end.

Definition typeEquality_BoolType
           DT `{FunctorLaws DT} `{BoolType <= DT}
           (R : Set) (rec : R -> TypeEqualityResult DT) (e : BoolType R)
  : TypeEqualityResult DT
  :=
    match e with
    | MkBoolType => fun t => isBoolType (proj1_sig t)
    end.

Global Instance TypeEquality_BoolType
       DT `{FunctorLaws DT} `{BoolType <= DT}
       T
  : ProgramAlgebra BoolType T (TypeEqualityResult DT)
  := {| programAlgebra := typeEquality_BoolType DT T|}.
