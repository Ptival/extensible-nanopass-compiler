From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
.

From ExtensibleCompiler.Theory Require Import
     Functor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context

    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
    `{! WellFormedSubFunctor Bool E}

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}

  .

  Inductive EvalRelation__Bool
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | BoolValue : forall b, EvalRelation__Bool EvalRelation__E (boolean b, boolean b)
  .

End Bool.
