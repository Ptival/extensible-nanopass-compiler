From Coq Require Import
     ssreflect
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
  := inject (App g a).

Definition lam
           {LT V L}
           `{FunctorLaws LT} `{FunctorLaws L}
           `{L supports (Lambda LT V)}
           t b
  : UniversalPropertyF L
  := inject (Lam t b).

Definition var
           {LT V L}
           `{FunctorLaws LT} `{FunctorLaws L}
            `{L supports (Lambda LT V)}
           v
  : UniversalPropertyF L
  := inject (Var v).
