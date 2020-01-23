From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Syntax.Types Require Import UnitType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition typeOf__UnitType
           {LT} `{FunctorLaws LT} `{LT supports UnitType}
  : forall {T}, MixinAlgebra Unit T (TypeOfResult LT)
  := fun _ rec '(Unit) => Some unitType'.

Global Instance TypeOf__Unit
       LT `{FunctorLaws LT} `{LT supports UnitType}
  : forall {T}, ProgramAlgebra Unit T (TypeOfResult LT)
  := fun _ => {| programAlgebra := typeOf__UnitType; |}.
