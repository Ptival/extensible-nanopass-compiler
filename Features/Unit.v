From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

From ExtensibleCompiler.Features Require Import Types.

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
  {
    intros A [].
    reflexivity.
  }
  {
    intros A B C f g [].
    reflexivity.
  }
Qed.

Definition unit
           {L} `{Functor L} `{FunctorLaws L} `{Unit <= L}
  : Fix L
  := inject MkUnit.

Definition unit__WF
           {L} `{Functor L} `{FunctorLaws L} `{Unit <= L}
  : WellFormedValue L
  := injectUniversalProperty MkUnit.

Global Instance EvalUnit
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports Unit}
       T
  : ProgramAlgebra Unit T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec 'MkUnit => proj1_sig unit__WF
    ;
  |}.

Inductive EvalUnit__WF (E V : Set -> Set)
          `{FunctorLaws E} `{FunctorLaws V}
          `{E supports Unit} `{V supports Unit}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | UnitValue : EvalUnit__WF E V Eval (unit__WF, unit__WF)
.
