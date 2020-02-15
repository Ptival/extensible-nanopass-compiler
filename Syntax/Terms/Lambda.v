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

Local Open Scope SubFunctor.

Inductive Lambda
          T `{FunctorLaws T}
          (B E : Set)
  : Set :=
| App (function : E) (argument : E)
| Lam (type : TypeFix T) (lambda : B -> E)
| Var (variable : B)
.
Arguments App {T _ _ B E}.
Arguments Lam {T _ _ B E}.
Arguments Var {T _ _ B E}.

Global Instance Functor__Lambda
       {T B} `{FunctorLaws T}
  : Functor (Lambda T B)
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
       {T B} `{FunctorLaws T}
  : FunctorLaws (Lambda T B).
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition app
           {T B E}
           `{FunctorLaws T} `{FunctorLaws E}
           `{E supports (Lambda T B)}
           g a
  : WellFormedValue E
  := inject (App g a).

Definition lam
           {T B E}
           `{FunctorLaws T} `{FunctorLaws E}
           `{E supports (Lambda T B)}
           t b
  : WellFormedValue E
  := inject (Lam t b).

Definition var
           {T B E}
           `{FunctorLaws T} `{FunctorLaws E}
            `{E supports (Lambda T B)}
           v
  : WellFormedValue E
  := inject (Var v).
