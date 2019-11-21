From Coq Require Import String.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive If1F (A : Set) : Set :=
| If1 (condition : A) (thenBranch : A)
.
Arguments If1 {A}.

Global Instance Functor_If1F : Functor If1F :=
  {|
    fmap := fun A B f '(If1 c t) => If1 (f c) (f t);
  |}.

Global Instance FunctorLaws_If1F : FunctorLaws (F := If1F).
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

Definition if1
           {L} `{Functor L} `{FunctorLaws L}
           `{If1F <= L} c t
  := injectUniversalProperty (If1 c t).

From ExtensibleCompiler.Theory Require Import Eval.

From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import Stuck.
From ExtensibleCompiler.Features Require Import Unit.

Global Instance EvalIf1
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports BoolF}
       `{O supports UnitF}
       `{O supports StuckF}
       T
  : ProgramAlgebra If1F T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(If1 condition thenBranch) =>
        match project (rec condition) with
        | Some (Bool b) =>
          if b
          then rec thenBranch
          else proj1_sig unit
        | None => proj1_sig (stuck "The condition of a unary branch did not evaluate to a boolean value")
        end
    ;
  |}.

(* Definition If1Induction *)
(*            (P : forall e, Fix If1F -> Prop) *)
(*            (H : forall c t, P (if1 c t)) *)
(*   : Algebra If1F { e | P e } *)
(*   := fun '(If1 (exist _ c _) (exist _ t _)) => *)
(*        exist _ (if1 c t) (H c t). *)
