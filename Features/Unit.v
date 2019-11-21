From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.
From ExtensibleCompiler.Theory Require Import SubFunctor.

Local Open Scope SubFunctor_scope.

Inductive UnitF (A: Set) : Set :=
| Unit
.
Arguments Unit {A}.

Global Instance Functor_UnitF : Functor UnitF :=
  {|
    fmap := fun A B f 'Unit => Unit;
  |}.

Global Instance FunctorLaws_UnitF : FunctorLaws (F := UnitF).
Proof.
  constructor.
  {
    intros A [].
    reflexivity.
  }
  {
    intros A B C f g [].
    reflexivity.
  }
Qed.

Definition unit
           {L} `{Functor L} `{FunctorLaws L} `{UnitF <= L}
  : WellFormedValue L
  := injectUniversalProperty Unit.
