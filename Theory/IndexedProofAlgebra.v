From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     IndexedSum1
     UniversalProperty
.

Local Open Scope SubFunctor.
Local Open Scope Sum1.

Class IndexedProofAlgebra (* cf. [iPAlgebra] *)
      (Label : Set) {I} F `{IndexedFunctor I F} A :=
  {
    indexedProofAlgebra (* cf. [ip_algebra] *)
    : IndexedAlgebra F A;
  }.

Definition indexedProofAlgebra'
           {Label I F A}
           `{IndexedFunctor I F}
           (PA : IndexedProofAlgebra Label F A)
  : IndexedAlgebra F A
  := indexedProofAlgebra (IndexedProofAlgebra := PA).

Global Instance
       IndexedProofAlgebraSum1
       {Label I} F G {A}
       `{IndexedFunctor I F} `{IndexedFunctor I G}
       {FAlg : IndexedProofAlgebra Label F A}
       {GAlg : IndexedProofAlgebra Label G A}
  : IndexedProofAlgebra Label (F + G) A
  :=
    {|
      indexedProofAlgebra :=
        fun i fg =>
          match fg with
          | iinl1 f => indexedProofAlgebra i f
          | iinr1 g => indexedProofAlgebra i g
          end
      ;
    |}.

Class WellFormedIndexedProofAlgebra (* cf. [iWF_Ind] *)
      {Label I F G}
      `{IndexedFunctor I F} `{IndexedFunctor I G}
      `{S : ! IndexedSubFunctor F G}
      {P : forall i, IndexedFix G i -> Prop}
      `(PA : ! IndexedProofAlgebra Label F (fun i => sig (P i)))
  :=
    {
      indexedProjEq
      : forall i e,
        proj1_sig (indexedProofAlgebra (IndexedProofAlgebra := PA) i e)
        =
        iWrapF i (iInj (IndexedSubFunctor := S) (indexedFmap i (fun i => proj1_sig (P := P i)) e));
    }.

(** TODO: document why we need this *)
Class WellFormedIndexedProofAlgebra2 (* cf. [WF_Ind2] *)
      {Label I F G H}
      `{IndexedFunctor I F} `{IndexedFunctor I G} `{IndexedFunctor I H}
      `{SG : ! IndexedSubFunctor F G} `{SH : ! IndexedSubFunctor F H}
      {P : forall i, (IndexedFix G i * IndexedFix H i) -> Prop}
      `(PA : ! IndexedProofAlgebra Label F (fun i => sig (P i)))
  :=
    {
      proj1Eq
      : forall i e,
        fst (proj1_sig (indexedProofAlgebra (IndexedProofAlgebra := PA) i e))
        =
        iWrapF i (iInj (IndexedSubFunctor := SG)
                       (indexedFmap i (fun i e => fst (proj1_sig (P := P i) e)) e));
      proj2Eq
      : forall i e,
        snd (proj1_sig (indexedProofAlgebra (IndexedProofAlgebra := PA) i e))
        =
        iWrapF i (iInj (IndexedSubFunctor := SH)
                       (indexedFmap i (fun i e => snd (proj1_sig (P := P i) e)) e));
    }.
