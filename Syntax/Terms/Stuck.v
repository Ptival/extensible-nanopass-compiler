From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     UniversalProperty
     SubFunctor
.

Local Open Scope SubFunctor_scope.

Inductive Stuck (A: Set) : Set :=
| MkStuck (reason : string)
.
Arguments MkStuck {A}.

Global Instance Functor_Stuck : Functor Stuck :=
  {|
    fmap := fun A B f '(MkStuck reason) => MkStuck reason;
  |}.

Global Instance FunctorLaws_Stuck : FunctorLaws Stuck.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition stuck
           {L} `{FunctorLaws L} `{L supports Stuck}
           (reason : string)
  : UniversalPropertyF L
  := inject (MkStuck reason).

Definition stuck_Fix
           {L} `{FunctorLaws L} `{L supports Stuck}
           (reason : string)
  : Fix L
  := proj1_sig (stuck reason).
