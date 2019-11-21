From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive BoolF (A: Set) : Set :=
| Bool (boolean : bool)
.
Arguments Bool {A}.

Global Instance Functor_BoolF : Functor BoolF :=
  {|
    fmap := fun A B f '(Bool b) => Bool b;
  |}.

Global Instance FunctorLaws_BoolF : FunctorLaws (F := BoolF).
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

Definition boolean
           {L} `{Functor L} `{FunctorLaws L}
           `{BoolF <= L} b
  := injectUniversalProperty (Bool b).
