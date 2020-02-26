From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     Sum1
.

Local Open Scope Sum1.

(**
[SubFunctor F E] should be read as "[F] is a sub-functor of [E]".
 *)
Class SubFunctor
      F E
      `{Functor F} `{Functor E}
  :=
    {

    inject : (* cf. [inj] *)
      forall {A}, F A -> E A;

    project : (* cf. [prj] *)
      forall {A}, E A -> option (F A);

    project_inject :
      forall {A} (fa : F A),
        project (inject fa) = Some fa;

    project_success :
      forall {A} {ga : E A} {fa : F A},
        project ga = Some fa ->
        ga = inject fa;

    wellFormedSubFunctor :
      forall (A B : Set) (f : A -> B) (fa : F A),
        fmap f (inject fa) = inject (fmap f fa)

  }.

Declare Scope SubFunctor.
Delimit Scope SubFunctor with SubFunctor.
Local Open Scope SubFunctor.

Notation "E 'supports' F" :=
  (SubFunctor F E)
    (at level 50)
  : SubFunctor.

(**
   Sadly notations prevent implicit insertion.
   cf. https://github.com/coq/coq/issues/11134
   So we write [SubFunctor] where we need it for conciseness...
 *)

Global Instance SubFunctor__Refl
       {F} `{Functor F}
  : SubFunctor F F.
Proof.
  refine (
      {|
        inject := fun _ fa => fa;
        project := fun _ fa => Some fa;
      |}
    ).
  - move => ?? //.
  - move => ??? [] //.
  - move => //.
Defined.

Global Instance SubFunctor__Left
       {F G H}
       `{Functor H}
       `{SubFunctor F G}
  : SubFunctor F (G + H).
Proof.
  refine (
      {|
        inject := fun _ fa => inl1 (inject fa);
        project := fun _ gh =>
                     match gh with
                     | inl1 ga => project ga
                     | inr1 _  => None
                     end;
      |}
    ).
  - move => ??; rewrite project_inject //.
  - move => ? [] // ?? /project_success -> //.
  - move => * /=; rewrite wellFormedSubFunctor //.
Defined.

Global Instance SubFunctor__Right
       {F G H}
       `{Functor G}
       `{SubFunctor F H}
  : SubFunctor F (G + H).
Proof.
  refine (
      {|
        inject := fun _ fa => inr1 (inject fa);
        project := fun _ gh =>
                     match gh with
                     | inl1 _  => None
                     | inr1 ha => project ha
                     end;
      |}
    ).
  - move => ??; rewrite project_inject //.
  - move => ? [] // ?? /project_success -> //.
  - move => * /=; rewrite wellFormedSubFunctor //.
Defined.

Definition subFunctorMendlerAlgebra
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
  : MendlerAlgebra F (Fix E)
  := fun A rec v =>
       wrapF (fmap rec (inject v)).
