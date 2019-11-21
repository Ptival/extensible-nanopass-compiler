From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

Notation "L 'supports' F" := (F <= L) (at level 50) : SubFunctor_scope.

Class Eval F R `{Functor F} `{Functor R} :=
  {
    evalAlgebra : MendlerAlgebra F (Fix R)
  }.

Global
  Instance
  EvalSum1 {F G R} `{Eval F R} `{Eval G R} : Eval (F + G) R
  | 2 :=
  {|
    evalAlgebra :=
      fun A rec v =>
        match v with
        | inl1 fa => evalAlgebra A rec fa
        | inr1 ga => evalAlgebra A rec ga
        end;
  |}.

Global
  Instance
  EvalSum1OutputL {F G} `{Functor F} `{Functor G} : Eval F (F + G)
  | 3 :=
  {|
    evalAlgebra := fun A rec v => wrapFix (inl1 (fmap rec v));
  |}.

Global
  Instance
  EvalSum1OutputR {F G} `{Functor F} `{Functor G} : Eval F (G + F)
  | 4 :=
  {|
    evalAlgebra := fun A rec v => wrapFix (inr1 (fmap rec v));
  |}.

Global Instance EvalRefl {F} `{Functor F} : Eval F F
  | 1 :=
  {|
    evalAlgebra := fun A rec v => wrapFix (fmap rec v);
  |}.
