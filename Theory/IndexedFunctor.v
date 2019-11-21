From ExtLib Require Import Programming.Extras.

Notation "I '-relation'" := ((I -> Prop) -> (I -> Prop)) (at level 50).

Class IndexedFunctor I (F : I-relation) : Prop :=
  {
    ifmap : forall {A B : I -> Prop} i, (forall i, A i -> B i) -> F A i -> F B i;
  }.

Class IndexedFunctorLaws {I F} `{IndexedFunctor I F} :=
  {
    ifmapFusion
    : forall (A B C : I -> Prop) i
        (f : forall i, A i -> B i)
        (g : forall i, B i -> C i)
        (a : F A i),
      ifmap i g (ifmap i f a) = ifmap i (fun i => compose (g i) (f i)) a;
    ifmapId
    : forall (A : I -> Prop) i (a : F A i),
        ifmap i (fun _ => id) a = a;
  }.
