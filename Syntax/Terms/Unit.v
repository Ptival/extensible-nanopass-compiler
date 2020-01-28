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

Definition unit
           {L} `{FunctorLaws L} `{L supports Unit}
  : UniversalPropertyF L
  := inject MkUnit.

Definition unitF
           {L} `{FunctorLaws L} `{L supports Unit}
  : Fix L
  := proj1_sig unit.

Section One.

  Context {L} `{FunctorLaws L} `{! L supports Unit}.

  Definition InductionAlgebra__Unit
             (P : forall (e : Fix L), FoldUP' e -> Prop)
             (H_unit : UniversalPropertyP P unitF)
    : Algebra Unit (sig (UniversalPropertyP P))
    := fun '(MkUnit) => exist _ _ (H_unit).

End One.

Section Two.

  Context {L} `{FunctorLaws L} `{! L supports Unit}.
  Context {M} `{FunctorLaws M} `{! M supports Unit}.

  Definition Induction2Algebra__Unit
             (P : forall (e : Fix L * Fix M), FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
             (H_unit : UniversalPropertyP2 P (unitF, unitF))
    : Algebra Unit (sig (UniversalPropertyP2 P))
    := fun '(MkUnit) => exist _ _ (H_unit).

End Two.
