From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
     If2
     Stuck
.

From ExtensibleCompiler.Theory Require Import
     Functor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section If2.

  Context

    {E}
    `{FunctorLaws E}
    `{! E supports If2}

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}

  .

  Inductive EvalRelation__If2
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | If2True : forall c t e t',
        EvalRelation__E (c, boolean true) ->
        EvalRelation__E (t, t') ->
        EvalRelation__If2 EvalRelation__E (if2 c t e, t')
    | If2False : forall c t e e',
        EvalRelation__E (c, boolean false) ->
        EvalRelation__E (e, e') ->
        EvalRelation__If2 EvalRelation__E (if2 c t e, e')
  .

End If2.
