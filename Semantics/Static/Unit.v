From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

From ExtensibleCompiler.Syntax.Types Require Import UnitType.

Local Open Scope SubFunctor_scope.

Definition typeOf_UnitType
           LT `{FunctorLaws LT} `{SubFunctor UnitType LT}
           (R : Set) (rec : R -> TypeOfResult LT)
           (e : Unit R)
  : TypeOfResult LT
  :=
    match e with
    | Unit => Some (injectUniversalProperty MkUnitType)
    end.

Global Instance TypeOf_Unit
       LT `{FunctorLaws LT} `{SubFunctor UnitType LT}
  : forall T, ProgramAlgebra Unit T (TypeOfResult LT)
  := fun T => {| programAlgebra := typeOf_UnitType LT T |}.
