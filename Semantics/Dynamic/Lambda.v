From Coq Require Import String.

From ExtensibleCompiler.Syntax.Terms Require Import Closure.
From ExtensibleCompiler.Syntax.Terms Require Import Lambda.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Environment.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition eval__Lambda
           {LT L} `{FunctorLaws LT}
           `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
           `{(L nat) supports (Closure L)}
           `{(L nat) supports Stuck}
  : MixinAlgebra (Lambda LT nat) (ValueFix (L nat)) (EvalResult (L nat))
  := fun rec e env =>
       match e with
       | App f a =>
         let f' := rec f env in
         match isClosure (proj1_sig f') with
         | Some (f, env') => rec f (insert (rec a env) env')
         | None           => stuck "Non-function in call position"
         end
       | Lam v b => stuck "TODO"
       | Var v   =>
         match lookup env v with
         | Some w => w
         | None   => stuck "Variable lookup failed"
         end
       end.

Global Instance EvalAlgebra__Lambda
       {LT L} `{FunctorLaws LT}
       `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
       `{(L nat) supports (Closure L)}
       `{(L nat) supports Stuck}
  : ProgramAlgebra Eval (Lambda LT nat) (ValueFix (L nat)) (EvalResult (L nat))
  := {| programAlgebra := eval__Lambda; |}.

(* TODO *)

(* Inductive Eval__Lambda *)
(*        {LT L} `{FunctorLaws LT} *)
(*        `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)} *)
(*        `{(L nat) supports (Closure L)} *)
(*        `{(L nat) supports Stuck} *)
(*   : (WellFormedValue L * WellFormedValue V) -> Prop *)
(*   := *)
(*   | LambdaTrue : forall c t e t', *)
(*       Eval (c, boolean true) -> *)
(*       Eval (t, t') -> *)
(*       Eval__Lambda Eval (lambda c t e, t') *)
(*   | Lambdaalse : forall c t e e', *)
(*       Eval (c, boolean false) -> *)
(*       Eval (e, e') -> *)
(*       Eval__Lambda Eval (lambda c t e, e') *)
(* . *)
