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

Inductive Lambda
          LT `{FLT : FunctorLaws LT}
          (V L : Set)
  : Set :=
| App (function : L) (argument : L)
| Lam (type : TypeFix LT) (lambda : V -> L)
| Var (variable : V)
.
Arguments App {LT _ _ V L}.
Arguments Lam {LT _ _ V L}.
Arguments Var {LT _ _ V L}.

Global Instance Functor__Lambda
       {LT V} `{FunctorLaws LT}
  : Functor (Lambda LT V)
  := {|
      fmap :=
        fun A B f v =>
          match v with
          | App g a => App (f g) (f a)
          | Lam t b => Lam t (fun v => f (b v))
          | Var v   => Var v
          end
      ;
    |}.

Global Instance FunctorLaws__Lambda
       {LT V} `{FunctorLaws LT}
  : FunctorLaws (Lambda LT V).
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition app
           {LT V L}
           `{FunctorLaws LT} `{FunctorLaws L}
           `{L supports (Lambda LT V)}
           g a
  : UniversalPropertyF L
  := injectUniversalProperty (App g a).

Definition lam
           {LT V L}
           `{FunctorLaws LT} `{FunctorLaws L}
           `{L supports (Lambda LT V)}
           t b
  : UniversalPropertyF L
  := injectUniversalProperty (Lam t b).

Definition var
           {LT V L}
           `{FunctorLaws LT} `{FunctorLaws L}
            `{L supports (Lambda LT V)}
           v
  : UniversalPropertyF L
  := injectUniversalProperty (Var v).
