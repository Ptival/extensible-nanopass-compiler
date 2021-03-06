From ExtensibleCompiler.Theory Require Import
     IndexedAlgebra
     IndexedFunctor
     IndexedSum1
.

Local Open Scope IndexedSum1.

Class IndexedSubFunctor
      {I} (F G : I-indexedPropFunctor)
      `{IndexedFunctor I F} `{IndexedFunctor I G}
  : Prop
  :=
    {
      iInj : forall {A i}, F A i -> G A i;
      iPrj : forall {A i}, G A i -> F A i \/ True;
    }.

Declare Scope IndexedSubFunctor.
Delimit Scope IndexedSubFunctor with IndexedSubFunctor.
Notation "F '<=' G" := (IndexedSubFunctor F G) : IndexedSubFunctor.
Local Open Scope IndexedSubFunctor.

Definition
  iInject
  {I} {F G : I-indexedPropFunctor}
  `{IndexedFunctor I F} `{IndexedFunctor I G}
  `{F <= G} {i}
  (fexp : F (IndexedFix G) i)
  : IndexedFix G i
  := iWrapF i (iInj fexp).

Definition
  iProject
  {I} {F G : I-indexedPropFunctor}
  `{IndexedFunctor I F} `{IndexedFunctor I G}
  `{F <= G} {i}
  (g : IndexedFix G i)
  : F (IndexedFix G) i \/ True
  := iPrj (iUnwrapF i g).

Global Instance IndexedSubFunctorRefl
       {I} {F} `{IndexedFunctor I F} : IndexedSubFunctor F F :=
  {|
    iInj := fun _ _ fa => fa;
    iPrj := fun _ _ fa => or_introl fa;
  |}.

Global Instance IndexedSubFunctor_inl1
       {I} {F G H}
       `{IndexedFunctor I F} `{IndexedFunctor I G} `{IndexedFunctor I H}
       `{F <= G}
  : F <= (G + H) :=
  {|
    iInj := fun _ _ fa => iinl1 (iInj fa);
    iPrj := fun _ _ gh =>
              match gh with
              | iinl1 g => iPrj g
              | iinr1 _ => or_intror Logic.I
              end;
  |}.

Global Instance IndexedSubFunctor_inr1
       {I} {F G H}
       `{IndexedFunctor I F} `{IndexedFunctor I G} `{IndexedFunctor I H}
       `{F <= H}
  : F <= (G + H) :=
  {|
    iInj := fun _ _ fa => iinr1 (iInj fa);
    iPrj := fun _ _ gh =>
             match gh with
             | iinl1 _  => or_intror Logic.I
             | iinr1 ha => iPrj ha
             end;
  |}.

(* Class WellFormedIndexedSubFunctor *)
(*       {I} {F G : I-indexedProp} *)
(*       `{IndexedFunctor I F} `{IndexedFunctor I G} *)
(*       `{F <= G} *)
(*   := *)
(*     { *)
(*       wellFormedIndexedSubFunctor *)
(*       : forall (A B : Set) (f : A -> B) (fa : F A), *)
(*         fmap f (inj fa) = inj (fmap f fa) *)
(*     }. *)

(* Global Instance WellFormedIndexedSubFunctorRefl *)
(*        {F} `{Functor F} *)
(*   : WellFormedIndexedSubFunctor F F := *)
(*   {| *)
(*     wellFormedIndexedSubFunctor := *)
(*       fun A B f fa => eq_refl; *)
(*   |}. *)
