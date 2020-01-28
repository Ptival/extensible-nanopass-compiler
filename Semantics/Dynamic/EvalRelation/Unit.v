From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Unit
.

From ExtensibleCompiler.Syntax.Types Require Import
     UnitType
.

From ExtensibleCompiler.Theory Require Import
     Functor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section Unit.

  Context

    {E}
    `{FunctorLaws E}
    `{! E supports Unit}
    `{!WellFormedSubFunctor Unit E}

    {V}
    `{FunctorLaws V}
    `{! V supports Unit}
    `{! WellFormedSubFunctor Unit V}

  .

  Inductive EvalRelation__Unit
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | UnitValue : EvalRelation__Unit EvalRelation__E (unit, unit)
  .

End Unit.
