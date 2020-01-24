From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

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
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : TypeFix LT
  := inject MkBoolType.

Definition boolType
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : Fix LT
  := proj1_sig boolType'.

Global Instance ReverseFoldUniversalProperty_boolType
           LT `{FunctorLaws LT} `{LT supports BoolType}
  : Fold__UP' boolType
  := proj2_sig boolType'.

Definition isBoolType
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : Fix LT -> bool
  := fun typ =>
       match project typ with
       | Some MkBoolType => true
       | None            => false
       end.

Definition typeEquality__BoolType
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : forall {T}, MixinAlgebra BoolType T (TypeEqualityResult LT)
  := fun _ rec '(MkBoolType) => fun t => isBoolType (proj1_sig t).

Global Instance TypeEquality__BoolType
       LT `{FunctorLaws LT} `{LT supports BoolType}
  : forall {T}, ProgramAlgebra TypeEquality BoolType T (TypeEqualityResult LT)
  := fun _ => {| programAlgebra := typeEquality__BoolType |}.
