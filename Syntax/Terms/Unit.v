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
           {L} `{FunctorLaws L} `{SubFunctor Unit L}
  : UniversalPropertyF L
  := injectUniversalProperty MkUnit.

Definition unit__Fix
           {L} `{FunctorLaws L} `{SubFunctor Unit L}
  : Fix L
  := proj1_sig unit.

Section One.

  Context {L} `{FunctorLaws L} `{! SubFunctor Unit L}.

  Definition InductionAlgebra__Unit
             (P : forall (e : Fix L), ReverseFoldUniversalProperty e -> Prop)
             (H_unit : UniversalPropertyP P unit__Fix)
    : Algebra Unit (sig (UniversalPropertyP P))
    := fun '(MkUnit) => exist _ _ (H_unit).

End One.

Section Two.

  Context {L} `{FunctorLaws L} `{! SubFunctor Unit L}.
  Context {M} `{FunctorLaws M} `{! SubFunctor Unit M}.

  Definition Induction2Algebra__Unit
             (P : forall (e : Fix L * Fix M),
                 ReverseFoldUniversalProperty (fst e) /\ ReverseFoldUniversalProperty (snd e) -> Prop
             )
             (H_unit : UniversalPropertyP2 P (unit__Fix, unit__Fix))
    : Algebra Unit (sig (UniversalPropertyP2 P))
    := fun '(MkUnit) => exist _ _ (H_unit).

End Two.
