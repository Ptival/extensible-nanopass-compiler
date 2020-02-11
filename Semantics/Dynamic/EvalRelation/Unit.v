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
     Algebra
     Functor
     IndexedFunctor
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
            (EvalRelation__E : (Fix E * Fix V) -> Prop)
    : (Fix E * Fix V) -> Prop
    :=
    | UnitValue : EvalRelation__Unit EvalRelation__E (unitF, unitF)
  .

  Global Instance IndexedFunctor_EvalRelation__Unit
    : IndexedFunctor (Fix E * Fix V) EvalRelation__Unit.
  Proof.
    constructor.
    move => A B i IH [].
    - econstructor 1; apply IH => //.
  Qed.

End Unit.
