From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSum1.

Local Open Scope IndexedSum1_scope.

Definition IndexedAlgebra {I} (F : I-indexedProp) A
  := forall i, F A i -> A i.

Definition IndexedMendlerAlgebra {I} (F : I-indexedProp) (A : I -> Prop) : Prop
  := forall i (R : I -> Prop), (forall i, R i -> A i) -> F R i -> A i.

Definition IndexedFix {I} (F : I-indexedProp) i : Prop
  := forall (A : I -> Prop), IndexedMendlerAlgebra F A -> A i.

Definition
  iMendlerFold
  {I} {F : I-indexedProp} {A : I -> Prop} (f : IndexedMendlerAlgebra F A) i
  : IndexedFix F i -> A i
  := fun e => e A f.

Definition
  iWrapFix
  {I} {F : I-indexedProp} i (unwrapped : F (IndexedFix F) i)
  : IndexedFix F i
  := fun A f
     => f i (IndexedFix F) (iMendlerFold f) unwrapped.

Definition
  ifold
  {I} {F : I-indexedProp} `{IndexedFunctor I F} {A : I -> Prop}
  (f : IndexedAlgebra F A) i (e : IndexedFix F i)
  : A i
  := iMendlerFold (fun i' r rec fa => f i' (indexedFmap i' rec fa)) i e.

Definition
  iUnwrapFix
  {I} {F : I-indexedProp} `{IndexedFunctor I F}
  : forall (i : I), IndexedFix F i -> F (IndexedFix F) i
  := ifold (fun i => indexedFmap i iWrapFix).
