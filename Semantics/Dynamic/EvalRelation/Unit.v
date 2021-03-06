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

Local Open Scope SubFunctor.

Section Unit.

  Context

    {E}
    `{Functor E}
    `{! E supports Unit}

    {V}
    `{Functor V}
    `{! V supports Unit}

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
