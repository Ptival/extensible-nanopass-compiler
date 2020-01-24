From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

(**

[ProgramAlgebra] captures those algebras that we will use for programming.
Because programs are computationally-revelant, we need [MixinAlgebra]s.

In order to distinguish some [ProgramAlgebra]s that would otherwise have the
same signature, each [ProgramAlgebra] is given a unique [Label].  This helps
the typeclass mechanism find the appropriate instance among a bunch of program
algebras with the same carrier types.

You can just create a new label with:
[Variant MyLabel := .]
The type does not need any inhabitant, we only use its type identity.

 *)
Class ProgramAlgebra (* cf. [FAlgebra] *)
      (Label : Set) F `{FunctorLaws F} T A :=
  {
    programAlgebra (* cf. [f_algebra] *)
    : MixinAlgebra F T A;
  }.

(**
Just like [programAlgebra], but when you want to provide the [ProgramAlgebra]
explicitly.
 *)
Definition programAlgebra'
           {Label F T A}
           `{FunctorLaws F}
      (PA : ProgramAlgebra Label F T A)
  := programAlgebra (ProgramAlgebra := PA).

(**
A version of [mendlerFold] specialized to handling [ProgramAlgebra]s.
Convenient to use because you can explicitly pass the algebra.
 *)
Definition foldProgramAlgebra
           {Label F O} `{FunctorLaws F}
           `{Alg : ! forall {T}, ProgramAlgebra Label F T O}
           (e : Fix F)
  : O
  := mendlerFold (fun _ => programAlgebra' Alg) e.

Global Instance
       ProgramAlgebraSum1 Label F G {T A}
       `{FAlg : ProgramAlgebra Label F T A}
       `{GAlg : ProgramAlgebra Label G T A}
  : ProgramAlgebra Label (F + G) T A
  :=
    {|
      programAlgebra :=
        fun rec v =>
          match v with
          | inl1 f => programAlgebra rec f
          | inr1 g => programAlgebra rec g
          end
      ;
    |}.

Global Instance
       ProgramAlgebraLeft {Label F G}
       `{FunctorLaws F}
       `{FunctorLaws G}
  : forall {T}, ProgramAlgebra Label F T (WellFormedValue (F + G))
  := fun T =>
    {|
      programAlgebra :=
        fun rec v => wrap__UP' (inl1 (fmap rec v))
      ;
    |}.

Global Instance
       ProgramAlgebraRight {Label F G}
       `{FunctorLaws F}
       `{FunctorLaws G}
  : forall {T}, ProgramAlgebra Label G T (WellFormedValue (F + G))
  := fun T =>
    {|
      programAlgebra :=
        fun rec v => wrap__UP' (inr1 (fmap rec v))
      ;
    |}.

(**

A program-producing [ProgramAlgebra] is well-formed when it properly dispatches
to its sub-algebras.

              programAlgebra FAlg
       F T -------------------------> A
        |                             =
        | inj                         =
        v                             =
       G T -------------------------> A
              programAlgebra GAlg

*)

(* Corresponds to [WF__FAlgebra] *)
Class WellFormedProgramAlgebra {Label F G T A}
      `{S : SubFunctor F G}
      `(FAlg : ProgramAlgebra Label F T A)
      `(GAlg : ProgramAlgebra Label G T A)
  :=
    {
      wellFormedProgramAlgebra
      : forall rec (fa : F T),
        @programAlgebra Label G _ _ _ _ _ rec (inj (SubFunctor := S) fa)
        =
        @programAlgebra Label F _ _ _ _ _ rec fa;
    }.

Global Instance
       WellFormedProgramAlgebraRefl {Label F T A}
       `{FAlg : ProgramAlgebra Label F T A}
  : WellFormedProgramAlgebra FAlg FAlg.
Proof.
  constructor.
  intros rec fa.
  unfold inj.
  unfold SubFunctorRefl.
  reflexivity.
Qed.

Global Instance
       WellFormedProgramAlgebraLeft
       {Label F G T A}
       `{FAlg : ProgramAlgebra Label F T A}
       `{GAlg : ProgramAlgebra Label G T A}
       {S : SubFunctor F G}
       {H} `{HAlg : ProgramAlgebra Label H T A}
       {WFFG : WellFormedProgramAlgebra FAlg GAlg}
  : WellFormedProgramAlgebra FAlg (ProgramAlgebraSum1 Label G H).
Proof.
  constructor.
  intros rec f.
  unfold inj.
  unfold SubFunctorLeft.
  simpl.
  rewrite wellFormedProgramAlgebra.
  reflexivity.
Qed.

Global Instance
       WellFormedProgramAlgebraRight
       {Label F G T A}
       `{FAlg : ProgramAlgebra Label F T A}
       `{GAlg : ProgramAlgebra Label G T A}
       {H} `{HAlg : ProgramAlgebra Label H T A}
       {FH : SubFunctor F H}
       {WFFH : WellFormedProgramAlgebra FAlg HAlg}
  : WellFormedProgramAlgebra FAlg (ProgramAlgebraSum1 Label G H).
Proof.
  constructor.
  intros rec f.
  unfold inj.
  unfold SubFunctorRight.
  simpl.
  rewrite wellFormedProgramAlgebra.
  reflexivity.
Qed.

Class WellFormedMendlerAlgebra (* cf. [WF_Malgebra] *)
      {Label F A}
      `{FunctorLaws F}
      (MAlg : forall T, ProgramAlgebra Label F T A)
  :=
    {
      wellFormedMendlerAlgebra (* cf. [wf_malgebra] *)
      : forall (T T' : Set) (f : T' -> T) (rec : T -> A) (ft : F T'),
        programAlgebra (ProgramAlgebra := MAlg T) rec (fmap f ft) =
        programAlgebra (ProgramAlgebra := MAlg T') (fun ft' => rec (f ft')) ft
    }.
