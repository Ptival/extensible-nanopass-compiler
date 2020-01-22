From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import Sum1.

Local Open Scope Sum1_scope.

(** While we technically don't need the [FunctorLaws] constraints, it's
convenient to put them here so that they are implicitly inserted everywhere. *)
Class SubFunctor (F G : Set -> Set)
      `{FunctorLaws F} `{FunctorLaws G}
  : Set :=
  {
    inj : forall {A}, F A -> G A;
    prj : forall {A}, G A -> option (F A);
  }.

Delimit Scope SubFunctor_scope with SubFunctor.

(* Notation "F '<=' G" := (SubFunctor F G) : SubFunctor_scope. *)

Local Open Scope SubFunctor_scope.

(**
   Sadly notations prevent implicit insertion.
   cf. https://github.com/coq/coq/issues/11134
   So we write [SubFunctor] where we need it for conciseness...
 *)

Definition
  project {F G}
  `{S : SubFunctor F G}
  (g : Fix G)
  : option (F (Fix G))
  := prj (unwrapFix g).

Global Instance SubFunctorRefl {F}
       `{FunctorLaws F} : SubFunctor F F :=
  {|
    inj := fun _ fa => fa;
    prj := fun _ fa => Some fa;
  |}.

Global Instance SubFunctorLeft {F G H}
       `{S : SubFunctor F G} `{FunctorLaws H}
  : SubFunctor F (G + H) :=
  {|
    inj := fun _ fa => inl1 (inj fa);
    prj := fun _ gh =>
             match gh with
             | inl1 ga => prj ga
             | inr1 _  => None
             end;
  |}.

Global Instance SubFunctorRight {F G H}
       `{S : SubFunctor F H} `{FunctorLaws G}
  : SubFunctor F (G + H) :=
  {|
    inj := fun _ fa => inr1 (inj fa);
    prj := fun _ gh =>
             match gh with
             | inl1 _  => None
             | inr1 ha => prj ha
             end;
  |}.

Definition
  subFunctorMendlerAlgebra {F G}
  `{S : SubFunctor F G}
  : MendlerAlgebra F (Fix G)
  := fun A rec v =>
       wrapFix (fmap rec (inj v)).

Class WellFormedSubFunctor F G
      `{SubFunctor F G}
  :=
    {
      wellFormedSubFunctor
      : forall (A B : Set) (f : A -> B) (fa : F A),
        fmap f (inj fa) = inj (fmap f fa)
    }.

Global Instance WellFormedSubFunctorRefl
       {F} `{FunctorLaws F}
  : WellFormedSubFunctor F F :=
  {|
    wellFormedSubFunctor :=
      fun A B f fa => eq_refl;
  |}.
