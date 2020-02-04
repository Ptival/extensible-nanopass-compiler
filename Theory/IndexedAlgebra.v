From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     IndexedFunctor
     IndexedSum1
.

Local Open Scope IndexedSum1_scope.

Definition IndexedAlgebra
           {I} (F : I-indexedPropFunctor) (A : I-indexedProp)
  : Prop
  := forall i, F A i -> A i.

Definition IndexedMendlerAlgebra
           {I} (F : I-indexedPropFunctor) (A : I-indexedProp)
  : Prop
  := forall i (R : I -> Prop), (forall i, R i -> A i) -> F R i -> A i.

Definition IndexedFix
           {I} (F : I-indexedPropFunctor) i
  : Prop
  := forall (A : I-indexedProp), IndexedMendlerAlgebra F A -> A i.

Definition
  iMendlerFold
  {I} {F : I-indexedPropFunctor} {A : I -> Prop} (f : IndexedMendlerAlgebra F A) i
  : IndexedFix F i -> A i
  := fun e => e A f.

Definition
  iWrapF
  {I} {F : I-indexedPropFunctor} i (unwrapped : F (IndexedFix F) i)
  : IndexedFix F i
  := fun A f
     => f i (IndexedFix F) (iMendlerFold f) unwrapped.

Definition
  ifold
  {I} {F : I-indexedPropFunctor} `{IndexedFunctor I F} {A : I-indexedProp}
  (f : IndexedAlgebra F A) i (e : IndexedFix F i)
  : A i
  := iMendlerFold (fun i' r rec fa => f i' (indexedFmap i' rec fa)) i e.

Definition
  iUnwrapF
  {I} {F : I-indexedPropFunctor} `{IndexedFunctor I F}
  : forall (i : I), IndexedFix F i -> F (IndexedFix F) i
  := ifold (fun i => indexedFmap i iWrapF).
