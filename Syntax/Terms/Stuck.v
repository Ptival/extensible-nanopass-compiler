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

Global Instance Functor__Stuck
  : Functor Stuck.
Proof.
  refine
    {|
      fmap := fun A B f '(MkStuck reason) => MkStuck reason;
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section Stuck.

  Context
    {E}
    `{Functor E}
    `{E supports Stuck}
    .

    Definition stuck
               (reason : string)
      : WellFormedValue E
      := injectUP' (MkStuck reason).

    Definition stuckF
               (reason : string)
      : Fix E
      := proj1_sig (stuck reason).

End Stuck.
