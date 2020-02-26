From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Unit
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.
Local Open Scope Sum1.

Inductive UnitType (A : Set) : Set :=
| MkUnitType : UnitType A
.
Arguments MkUnitType {A}.

Global Instance Functor__UnitType
  : Functor UnitType.
Proof.
  refine
    {|
      fmap := fun A B f 'MkUnitType => MkUnitType;
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section UnitType.

  Context
    {T}
    `{Functor T}
    `{T supports UnitType}
  .

  Definition unitType'
    : TypeFix T
    := injectUP' MkUnitType.

  Definition unitType
    : Fix T
    := proj1_sig unitType'.

  Global Instance FoldUP'__unitType
    : FoldUP' unitType
    := proj2_sig unitType'.

  Definition isUnitType
    : Fix T -> bool
    := fun typ =>
         match projectUP' typ with
         | Some MkUnitType => true
         | None            => false
         end.

End UnitType.
