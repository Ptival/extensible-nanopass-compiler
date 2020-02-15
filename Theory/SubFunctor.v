From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     Sum1
.

Local Open Scope Sum1.

(** While we technically don't need the [FunctorLaws] constraints, it's
convenient to put them here so that they are implicitly inserted everywhere. *)
Class SubFunctor (F G : Set -> Set)
      `{FunctorLaws F} `{FunctorLaws G}
  : Set :=
  {
    inj : forall {A}, F A -> G A;
    prj : forall {A}, G A -> option (F A);
    inj_prj : forall {A} {ga : G A} {fa : F A},
        prj ga = Some fa ->
        ga = inj fa;
    prj_inj : forall {A} (fa : F A),
        prj (inj fa) = Some fa;
  }.

Declare Scope SubFunctor.
Delimit Scope SubFunctor with SubFunctor.

Notation "L 'supports' F" := (SubFunctor F L) (at level 50) : SubFunctor.

Local Open Scope SubFunctor.

(**
   Sadly notations prevent implicit insertion.
   cf. https://github.com/coq/coq/issues/11134
   So we write [SubFunctor] where we need it for conciseness...
 *)

Global Instance SubFunctorRefl {F}
       `{FunctorLaws F} : SubFunctor F F.
Proof.
  refine (
      {|
        inj := fun _ fa => fa;
        prj := fun _ fa => Some fa;
      |}
    ).
  - move => ??? [] //.
  - move => ?? //.
Defined.

Global Instance SubFunctorLeft {F G H}
       `{S : SubFunctor F G} `{FunctorLaws H}
  : SubFunctor F (G + H).
Proof.
  refine (
      {|
        inj := fun _ fa => inl1 (inj fa);
        prj := fun _ gh =>
                 match gh with
                 | inl1 ga => prj ga
                 | inr1 _  => None
                 end;
      |}
    ).
  {
    move => ? [] => // ?? EQ.
    rewrite (inj_prj EQ) //.
  }
  {
    move => ??.
    rewrite prj_inj //.
  }
Defined.

Global Instance SubFunctorRight {F G H}
       `{S : SubFunctor F H} `{FunctorLaws G}
  : SubFunctor F (G + H).
Proof.
  refine (
      {|
        inj := fun _ fa => inr1 (inj fa);
        prj := fun _ gh =>
                 match gh with
                 | inl1 _  => None
                 | inr1 ha => prj ha
                 end;
      |}
    ).
  {
    move => ? [] => // ?? EQ.
    rewrite (inj_prj EQ) //.
  }
  {
    move => ??.
    rewrite prj_inj //.
  }
Defined.

Definition
  subFunctorMendlerAlgebra {F G}
  `{S : SubFunctor F G}
  : MendlerAlgebra F (Fix G)
  := fun A rec v =>
       wrapF (fmap rec (inj v)).

Class WellFormedSubFunctor F G
      `{SubFunctor F G}
  :=
    {
      wellFormedSubFunctor
      : forall (A B : Set) (f : A -> B) (fa : F A),
        fmap f (inj fa) = inj (fmap f fa)
    }.

Global Instance WellFormedSubFunctor_Refl
       {F} `{FunctorLaws F}
  : WellFormedSubFunctor F F :=
  {|
    wellFormedSubFunctor :=
      fun A B f fa => eq_refl;
  |}.

Global Instance WellFormedSubFunctor_Left
       {F G H}
       `{FunctorLaws F} `{FunctorLaws G} `{FunctorLaws H}
       `{S : ! SubFunctor F G}
       `{! WellFormedSubFunctor F G}
  : WellFormedSubFunctor F (G + H).
Proof.
  refine (
      {|
        wellFormedSubFunctor :=
          fun A B f fa => _;
      |}
    ).
  rewrite /= wellFormedSubFunctor //.
Defined.

Global Instance WellFormedSubFunctor_Right
       {F G H}
       `{FunctorLaws F} `{FunctorLaws G} `{FunctorLaws H}
       `{S : ! SubFunctor F H}
       `{! WellFormedSubFunctor F H}
  : WellFormedSubFunctor F (G + H).
Proof.
  refine (
      {|
        wellFormedSubFunctor :=
          fun A B f fa => _;
      |}
    ).
  rewrite /= wellFormedSubFunctor //.
Defined.
