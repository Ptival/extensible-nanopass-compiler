From Coq Require Import
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Closure
     Lambda
     Stuck
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Environment
     Eval
     Functor
     ProgramAlgebra
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section Lambda.

  Context

    {T}
    `{FunctorLaws T}

    {E}
    `{! forall B, Functor (E B)}
    `{! forall B, FunctorLaws (E B)}
    `{(E nat) supports (Closure E)}
    `{(E nat) supports Stuck}

  .

  Definition eval__Lambda
    : MixinAlgebra (Lambda T nat) (ValueFix (E nat)) (EvalResult (E nat))
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

  Global Instance Eval__Lambda
    : ProgramAlgebra ForEval (Lambda T nat) (ValueFix (E nat)) (EvalResult (E nat))
    := {| programAlgebra := eval__Lambda; |}.

End Lambda.
