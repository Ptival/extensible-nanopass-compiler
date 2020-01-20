From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import Stuck.
From ExtensibleCompiler.Features Require Import Types.
From ExtensibleCompiler.Features Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

From ExtensibleCompiler.Types Require Import BoolType.
From ExtensibleCompiler.Types Require Import UnitType.

Local Open Scope SubFunctor_scope.

Inductive If1 (A : Set) : Set :=
| MkIf1 (condition : A) (thenBranch : A)
.
Arguments MkIf1 {A}.

Global Instance Functor_If1 : Functor If1
  := {| fmap := fun A B f '(MkIf1 c t) => MkIf1 (f c) (f t); |}.

Global Instance FunctorLaws_If1 : FunctorLaws If1.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition if1
           {L} `{Functor L} `{FunctorLaws L}
           `{If1 <= L} c t
  := injectUniversalProperty (MkIf1 c t).

Global Instance EvalIf1
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports Bool}
       `{O supports Unit}
       `{O supports Stuck}
       T
  : ProgramAlgebra If1 T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(MkIf1 condition thenBranch) =>
        match project (rec condition) with
        | Some (MkBool b) =>
          if b
          then rec thenBranch
          else proj1_sig unit__WF
        | None => proj1_sig (stuck "The condition of a unary branch did not evaluate to a boolean value")
        end
    ;
  |}.

Inductive EvalIf1__WF (E V : Set -> Set)
          `{FunctorLaws E} `{FunctorLaws V}
          `{E supports If1} `{V supports Bool} `{V supports Unit}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | If1True : forall c t t',
      Eval (c, boolean__WF true) ->
      Eval (t, t') ->
      EvalIf1__WF E V Eval (if1 c t, t')
  | If1alse : forall c t,
      Eval (c, boolean__WF false) ->
      EvalIf1__WF E V Eval (if1 c t, unit__WF)
.

(* Definition If1Induction *)
(*            (P : forall e, Fix If1 -> Prop) *)
(*            (H : forall c t, P (if1 c t)) *)
(*   : Algebra If1 { e | P e } *)
(*   := fun '(If1 (exist _ c _) (exist _ t _)) => *)
(*        exist _ (if1 c t) (H c t). *)
