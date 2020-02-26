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

Local Open Scope SubFunctor.
Local Open Scope Sum1.

Inductive Unit (A: Set) : Set :=
| MkUnit
.
Arguments MkUnit {A}.

Global Instance Functor__Unit
  : Functor Unit.
Proof.
  refine
    {|
      fmap := fun A B f 'MkUnit => MkUnit;
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section Unit.

  Context
    {E}
    `{Functor E}
    `{E supports Unit}
  .

  Definition unit
    : WellFormedValue E
    := injectUP' MkUnit.

  Definition unitF
    : Fix E
    := proj1_sig unit.

  Definition InductionAlgebra__Unit
             (P : forall (e : Fix E), FoldUP' e -> Prop)
             (IH__unit : UniversalPropertyP P unitF)
    : Algebra Unit (sig (UniversalPropertyP P))
    := fun '(MkUnit) => exist _ _ (IH__unit).

End Unit.

Section Unit.

  Context
    {E}
    `{Functor E}
    `{E supports Unit}

    {M}
    `{Functor M}
    `{M supports Unit}
  .

  Definition Induction2Algebra__Unit
             (P :
                forall (e : Fix E * Fix M),
                  FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
             (IH__unit : UniversalPropertyP2 P (unitF, unitF))
    : Algebra Unit (sig (UniversalPropertyP2 P))
    := fun '(MkUnit) => exist _ _ (IH__unit).

End Unit.
