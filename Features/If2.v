From Coq Require Import String.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

Inductive If2F (A : Set) : Set :=
| If2 (condition : A) (thenBranch : A) (elseBranch : A)
.
Arguments If2 {A}.

Global Instance Functor_If2F : Functor If2F :=
  {|
    fmap := fun A B f '(If2 c t e) => If2 (f c) (f t) (f e);
  |}.

Global Instance FunctorLaws_If2F : FunctorLaws (F := If2F).
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

Definition if2
           {L} `{Functor L} `{FunctorLaws L}
           `{If2F <= L} condition thenBranch elseBranch
  := injectUniversalProperty (If2 condition thenBranch elseBranch).

From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import Unit.
From ExtensibleCompiler.Features Require Import Stuck.

Global Instance EvalIf2
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports BoolF}
       `{O supports StuckF}
       T
  : ProgramAlgebra If2F T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(If2 condition thenBranch elseBranch) =>
        match project (rec condition) with
        | Some (Bool b) =>
          if b
          then rec thenBranch
          else rec elseBranch
        | None => proj1_sig (stuck "The condition of a binary branch did not evaluate to a boolean value")
        end
    ;
  |}.
