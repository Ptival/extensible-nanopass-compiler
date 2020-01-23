From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.
From ExtensibleCompiler.Syntax.Types Require Import UnitType.

Local Open Scope SubFunctor_scope.

Inductive If1 (A : Set) : Set :=
| MkIf1 (condition : A) (thenBranch : A)
.
Arguments MkIf1 {A}.

Global Instance Functor_If1 : Functor If1
  := {| fmap := fun A B f '(MkIf1 c t) => MkIf1 (f c) (f t); |}.

Global Instance FunctorLaws_If1 : FunctorLaws If1.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition if1
           {L} `{FunctorLaws L} `{L supports If1} c t
  : UniversalPropertyF L
  := injectUniversalProperty (MkIf1 c t).

Definition if1_Fix
           {L} `{FunctorLaws L} `{L supports If1} c t
  : Fix L
  := proj1_sig (if1 c t).

(* Definition If1Induction *)
(*            (P : forall e, Fix If1 -> Prop) *)
(*            (H : forall c t, P (if1 c t)) *)
(*   : Algebra If1 { e | P e } *)
(*   := fun '(If1 (exist _ c _) (exist _ t _)) => *)
(*        exist _ (if1 c t) (H c t). *)
