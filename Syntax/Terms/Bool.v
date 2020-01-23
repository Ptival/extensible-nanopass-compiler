From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive Bool (A: Set) : Set :=
| MkBool (boolean : bool)
.
Arguments MkBool {A}.

Global Instance Functor_Bool : Functor Bool :=
  {|
    fmap := fun A B f '(MkBool b) => MkBool b;
  |}.

Global Instance FunctorLaws_Bool : FunctorLaws Bool.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition boolean
           {L} `{FunctorLaws L} `{SubFunctor Bool L}
           (b : bool)
  : UniversalPropertyF L
  := injectUniversalProperty (MkBool b).

Definition boolean_Fix
           {L} `{FunctorLaws L} `{SubFunctor Bool L}
           (b : bool)
  : Fix L
  := proj1_sig (boolean b).

Section One.

  Context {L} `{FunctorLaws L} `{! SubFunctor Bool L}.

  Definition InductionAlgebra_Bool
             (P : forall (e : Fix L), ReverseFoldUniversalProperty e -> Prop)
             (H_boolean : forall b, UniversalPropertyP P (boolean_Fix b))
    : Algebra Bool (sig (UniversalPropertyP P))
    := fun '(MkBool b) => exist _ _ (H_boolean b).

End One.

Section Two.

  Context {L} `{FunctorLaws L} `{! SubFunctor Bool L}.
  Context {M} `{FunctorLaws M} `{! SubFunctor Bool M}.

  Definition Induction2Algebra_Bool
             (P : forall (e : Fix L * Fix M),
                 ReverseFoldUniversalProperty (fst e) /\ ReverseFoldUniversalProperty (snd e) -> Prop
             )
             (H_boolean : forall b, UniversalPropertyP2 P (boolean_Fix b, boolean_Fix b))
    : Algebra Bool (sig (UniversalPropertyP2 P))
    := fun '(MkBool b) => exist _ _ (H_boolean b).

End Two.
