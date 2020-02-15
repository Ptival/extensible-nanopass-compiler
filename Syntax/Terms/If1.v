From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Bool
     Terms.Stuck
     Terms.Unit
     Types.BoolType
     Types.UnitType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     ProofAlgebra
     SubFunctor
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.

Inductive If1 (A : Set) : Set :=
| MkIf1 (condition : A) (thenBranch : A)
.
Arguments MkIf1 {A}.

Global Instance Functor_If1 : Functor If1
  := {| fmap := fun A B f '(MkIf1 c t) => MkIf1 (f c) (f t) |}.

Global Instance FunctorLaws_If1 : FunctorLaws If1.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition if1
           {E} `{FunctorLaws E} `{E supports If1} c t
  : WellFormedValue E
  := inject (MkIf1 c t).

Definition if1F
           {E} `{FunctorLaws E} `{E supports If1} (c t : Fix E)
  : Fix E
  := wrapF (inj (MkIf1 c t)).

Definition if1F'
           {E} `{FunctorLaws E} `{E supports If1} c t
  : Fix E
  := proj1_sig (if1 c t).

(* Definition If1Induction *)
(*            (P : forall e, Fix If1 -> Prop) *)
(*            (H : forall c t, P (if1 c t)) *)
(*   : Algebra If1 { e | P e } *)
(*   := fun '(If1 (exist _ c _) (exist _ t _)) => *)
(*        exist _ (if1 c t) (H c t). *)
