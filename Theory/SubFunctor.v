From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import Sum1.

Local Open Scope Sum1_scope.

Class SubFunctor (F G : Set -> Set) `{Functor F} `{Functor G} : Set :=
  {
    inj : forall {A}, F A -> G A;
    prj : forall {A}, G A -> option (F A);
  }.

Delimit Scope SubFunctor_scope with SubFunctor.
Notation "F '<=' G" := (SubFunctor F G) : SubFunctor_scope.
Local Open Scope SubFunctor_scope.

Definition
  inject
  {F G} `{Functor F} `{Functor G} `{F <= G}
  (fexp : F (Fix G))
  : Fix G
  := wrapFix (inj fexp).

Definition
  project
  {F G} `{Functor F} `{Functor G} `{F <= G}
  (g : Fix G)
  : option (F (Fix G))
  := prj (unwrapFix g).

Global Instance SubFunctorRefl
       {F} `{Functor F} : SubFunctor F F :=
  {|
    inj := fun _ fa => fa;
    prj := fun _ fa => Some fa;
  |}.

Global Instance SubFunctorLeft
       {F G H} `{Functor F} `{Functor G} `{Functor H} `{FG : F <= G}
  : F <= (G + H) :=
  {|
    inj := fun _ fa => inl1 (inj fa);
    prj := fun _ gh =>
             match gh with
             | inl1 ga => prj ga
             | inr1 _  => None
             end;
  |}.

Global Instance SubFunctorRight
       {F G H} `{Functor F} `{Functor G} `{Functor H} `{FH : F <= H}
  : F <= (G + H) :=
  {|
    inj := fun _ fa => inr1 (inj fa);
    prj := fun _ gh =>
             match gh with
             | inl1 _  => None
             | inr1 ha => prj ha
             end;
  |}.

Definition
  subFunctorMendlerAlgebra
  {F G} `{Functor F} `{Functor G} `{F <= G}
  : MendlerAlgebra F (Fix G)
  := fun A rec v =>
       wrapFix (fmap rec (inj v)).

Class WellFormedSubFunctor
      F G `{Functor F} `{Functor G} `{F <= G}
  :=
    {
      wellFormedSubFunctor
      : forall (A B : Set) (f : A -> B) (fa : F A),
        fmap f (inj fa) = inj (fmap f fa)
    }.

Global Instance WellFormedSubFunctorRefl
       {F} `{Functor F}
  : WellFormedSubFunctor F F :=
  {|
    wellFormedSubFunctor :=
      fun A B f fa => eq_refl;
  |}.
