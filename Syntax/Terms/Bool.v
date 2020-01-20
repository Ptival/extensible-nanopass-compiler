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

Inductive Bool (A: Set) : Set :=
| MkBool (boolean : bool)
.
Arguments MkBool {A}.

Global Instance Functor_Bool : Functor Bool :=
  {|
    fmap := fun A B f '(MkBool b) => MkBool b;
  |}.

Global Instance FunctorLaws_Bool : FunctorLaws Bool.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition boolean
           {L} `{Functor L} `{FunctorLaws L}
           `{Bool <= L} b
  : Fix L
  := inject (MkBool b).

Definition boolean__WF
           {L} `{Functor L} `{FunctorLaws L}
           `{Bool <= L} b
  : WellFormedValue L
  := injectUniversalProperty (MkBool b).

Global Instance EvalBoolWellFormedValue
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports Bool}
       T
  : ProgramAlgebra Bool T (WellFormedValue O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(MkBool b) => boolean__WF b
    ;
  |}.

Global Instance EvalBoolix
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports Bool}
       T
  : ProgramAlgebra Bool T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(MkBool b) => boolean b
    ;
  |}.

Inductive EvalBool (E V : Set -> Set)
          `{FunctorLaws E} `{FunctorLaws V}
          `{E supports Bool} `{V supports Bool}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | BoolValue : forall b, EvalBool E V Eval (boolean__WF b, boolean__WF b)
.
