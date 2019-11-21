From Coq Require Import String.

From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.
From ExtensibleCompiler.Theory Require Import SubFunctor.

Local Open Scope SubFunctor_scope.

Inductive StuckF (A: Set) : Set :=
| Stuck (reason : string)
.
Arguments Stuck {A}.

Global Instance Functor_StuckF : Functor StuckF :=
  {|
    fmap := fun A B f '(Stuck reason) => Stuck reason;
  |}.

Global Instance FunctorLaws_StuckF : FunctorLaws (F := StuckF).
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

Definition stuck
           {L} `{Functor L} `{FunctorLaws L} `{StuckF <= L}
           (reason : string)
  : WellFormedValue L
  := injectUniversalProperty (Stuck reason).
