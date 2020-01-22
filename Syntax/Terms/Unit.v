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

Definition unit'
           {L} `{FunctorLaws L} `{SubFunctor Unit L}
  : UniversalPropertyF L
  := injectUniversalProperty MkUnit.

Definition unit
           {L} `{FunctorLaws L} `{SubFunctor Unit L}
  : Fix L
  := proj1_sig unit'.

Global Instance EvalUnit
       {O} `{FunctorLaws O}
       `{S : ! SubFunctor Unit O}
       T
  : ProgramAlgebra Unit T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec 'MkUnit => unit
    ;
  |}.

Inductive EvalUnit__WF
          {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! SubFunctor Unit E} `{! SubFunctor Unit V}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | UnitValue : EvalUnit__WF Eval (unit', unit')
.
