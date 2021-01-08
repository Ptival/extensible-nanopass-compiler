From ExtensibleCompiler.Theory Require Import
    Functor
.

Notation "I '-indexedProp'" := (I -> Prop) (at level 50, only parsing).
Notation "I '-indexedPropFunctor'" := (I-indexedProp -> I-indexedProp) (at level 50).

Class IndexedFunctor I (F : I-indexedPropFunctor) : Prop :=
  {
    indexedFmap : forall {A B : I -> Prop} i, (forall i, A i -> B i) -> F A i -> F B i;
  }.

Class IndexedFunctorLaws {I F} `{IndexedFunctor I F} :=
  {

    indexedFmapFusion
    : forall (A B C : I -> Prop) i
        (f : forall i, A i -> B i)
        (g : forall i, B i -> C i)
        (a : F A i),
      indexedFmap i g (indexedFmap i f a) = indexedFmap i (fun i => compose (g i) (f i)) a;

    indexedFmapId
    : forall (A : I -> Prop) i (a : F A i),
        indexedFmap i (fun _ => id) a = a;

  }.
