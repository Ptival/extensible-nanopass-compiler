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
          T `{Functor T}
          (B E : Set)
  : Set :=
| App (function : E) (argument : E)
| Lam (type : TypeFix T) (lambda : B -> E)
| Var (variable : B)
.
Arguments App {T _ B E}.
Arguments Lam {T _ B E}.
Arguments Var {T _ B E}.

Global Instance Functor__Lambda
       {T B} `{Functor T}
  : Functor (Lambda T B).
Proof.
  refine
    {|
      fmap :=
        fun A B f v =>
          match v with
          | App g a => App (f g) (f a)
          | Lam t b => Lam t (fun v => f (b v))
          | Var v   => Var v
          end
      ;
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Definition app
           {T B E}
           `{Functor T} `{Functor E}
           `{E supports (Lambda T B)}
           g a
  : WellFormedValue E
  := injectUP' (App g a).

Definition lam
           {T B E}
           `{Functor T} `{Functor E}
           `{E supports (Lambda T B)}
           t b
  : WellFormedValue E
  := injectUP' (Lam t b).

Definition var
           {T B E}
           `{Functor T} `{Functor E}
            `{E supports (Lambda T B)}
           v
  : WellFormedValue E
  := injectUP' (Var v).
