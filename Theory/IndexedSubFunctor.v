From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSum1.

Local Open Scope IndexedSum1_scope.

Class IndexedSubFunctor
      {I} (F G : I-relation)
      `{IndexedFunctor I F} `{IndexedFunctor I G}
  : Prop
  :=
    {
      iInj : forall {A i}, F A i -> G A i;
      iPrj : forall {A i}, G A i -> F A i \/ True;
    }.

Delimit Scope IndexedSubFunctor_scope with IndexedSubFunctor.
Notation "F '<=' G" := (IndexedSubFunctor F G) : IndexedSubFunctor_scope.
Local Open Scope IndexedSubFunctor_scope.

Definition
  iInject
  {I} {F G : I-relation} `{IndexedFunctor I F} `{IndexedFunctor I G} `{F <= G} {i}
  (fexp : F (IndexedFix G) i)
  : IndexedFix G i
  := iWrapFix i (iInj fexp).

Definition
  iProject
  {I} {F G : I-relation} `{IndexedFunctor I F} `{IndexedFunctor I G} `{F <= G} {i}
  (g : IndexedFix G i)
  : F (IndexedFix G) i \/ True
  := iPrj (iUnwrapFix i g).

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
(*       {I} {F G : I-relation} *)
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
