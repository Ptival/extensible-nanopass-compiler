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

Local Open Scope SubFunctor.

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

Section Stuck.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Stuck}
    .

    Definition stuck
               (reason : string)
      : WellFormedValue E
      := inject (MkStuck reason).

    Definition stuckF
               (reason : string)
      : Fix E
      := proj1_sig (stuck reason).

End Stuck.
