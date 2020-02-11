From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

Inductive Unit (A: Set) : Set :=
| MkUnit
.
Arguments MkUnit {A}.

Global Instance Functor_Unit : Functor Unit :=
  {|
    fmap := fun A B f 'MkUnit => MkUnit;
  |}.

Global Instance FunctorLaws_Unit : FunctorLaws Unit.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Section Unit.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Unit}
  .

  Definition unit
    : WellFormedValue E
    := inject MkUnit.

  Definition unitF
    : Fix E
    := proj1_sig unit.

  Definition InductionAlgebra__Unit
             (P : forall (e : Fix E), FoldUP' e -> Prop)
             (H_unit : UniversalPropertyP P unitF)
    : Algebra Unit (sig (UniversalPropertyP P))
    := fun '(MkUnit) => exist _ _ (H_unit).

End Unit.

Section Unit.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Unit}

    {M}
    `{FunctorLaws M}
    `{! M supports Unit}
  .

  Definition Induction2Algebra__Unit
             (P : forall (e : Fix E * Fix M), FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
             (H_unit : UniversalPropertyP2 P (unitF, unitF))
    : Algebra Unit (sig (UniversalPropertyP2 P))
    := fun '(MkUnit) => exist _ _ (H_unit).

End Unit.
