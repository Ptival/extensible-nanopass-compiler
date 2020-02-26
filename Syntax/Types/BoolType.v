From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProofAlgebra
     ProgramAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.

Inductive BoolType (A : Set) : Set :=
| MkBoolType : BoolType A
.
Arguments MkBoolType {A}.

Global Instance Functor__BoolType
  : Functor BoolType.
Proof.
  refine {| fmap := fun A B f 'MkBoolType => MkBoolType |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section BoolType.

  Context
    {T}
    `{Functor T}
    `{T supports BoolType}
  .

  Definition boolType'
    : TypeFix T
    := injectUP' MkBoolType.

  Definition boolType
    : Fix T
    := proj1_sig boolType'.

  Global Instance FoldUP'__boolType
    : FoldUP' boolType
    := proj2_sig boolType'.

  Definition isBoolType
    : Fix T -> bool
    := fun typ =>
         match projectUP' typ with
         | Some MkBoolType => true
         | None            => false
         end.

End BoolType.
