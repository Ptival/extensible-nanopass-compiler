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

*)

Class ProgramAlgebra (* cf. [FAlgebra] *)
      F `{FunctorLaws F} T A :=
  {
    programAlgebra (* cf. [f_algebra] *)
    : MixinAlgebra T F A;
  }.

(**
Just like [programAlgebra], but when you want to provide the [ProgramAlgebra]
explicitly.
*)
Definition programAlgebra'
           {F T A}
           `{FunctorLaws F}
      (PA : ProgramAlgebra F T A)
  := programAlgebra (ProgramAlgebra := PA).

Global Instance
       ProgramAlgebraSum1 F G {T A}
       `{FAlg : ProgramAlgebra F T A}
       `{GAlg : ProgramAlgebra G T A}
  : ProgramAlgebra (F + G) T A
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
       ProgramAlgebraLeft {F G}
       `{FunctorLaws F}
       `{FunctorLaws G}
  : forall {T}, ProgramAlgebra F T (WellFormedValue (F + G))
  := fun T =>
    {|
      programAlgebra :=
        fun rec v => reverseFoldWrapFix (inl1 (fmap rec v))
      ;
    |}.

Global Instance
       ProgramAlgebraRight {F G}
       `{FunctorLaws F}
       `{FunctorLaws G}
  : forall {T}, ProgramAlgebra G T (WellFormedValue (F + G))
  := fun T =>
    {|
      programAlgebra :=
        fun rec v => reverseFoldWrapFix (inr1 (fmap rec v))
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
Class WellFormedProgramAlgebra {F G T A}
      `{S : SubFunctor F G}
      `(FAlg : ProgramAlgebra F T A)
      `(GAlg : ProgramAlgebra G T A)
  :=
    {
      wellFormedProgramAlgebra
      : forall rec (fa : F T),
        @programAlgebra G _ _ _ _ _ rec (inj (SubFunctor := S) fa)
        =
        @programAlgebra F _ _ _ _ _ rec fa;
    }.

Global Instance
       WellFormedProgramAlgebraRefl {F T A}
       `{FAlg : ProgramAlgebra F T A}
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
       {F G T A}
       `{FAlg : ProgramAlgebra F T A}
       `{GAlg : ProgramAlgebra G T A}
       {S : SubFunctor F G}
       {H} `{HAlg : ProgramAlgebra H T A}
       {WFFG : WellFormedProgramAlgebra FAlg GAlg}
  : WellFormedProgramAlgebra FAlg (ProgramAlgebraSum1 G H).
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
       {F G T A}
       `{FAlg : ProgramAlgebra F T A}
       `{GAlg : ProgramAlgebra G T A}
       {H} `{HAlg : ProgramAlgebra H T A}
       {FH : SubFunctor F H}
       {WFFH : WellFormedProgramAlgebra FAlg HAlg}
  : WellFormedProgramAlgebra FAlg (ProgramAlgebraSum1 G H).
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
      {F A}
      `{FunctorLaws F}
      (MAlg : forall T, ProgramAlgebra F T A)
  :=
    {
      wellFormedMendlerAlgebra (* cf. [wf_malgebra] *)
      : forall (T T' : Set) (f : T' -> T) (rec : T -> A) (ft : F T'),
        programAlgebra (ProgramAlgebra := MAlg T) rec (fmap f ft) =
        programAlgebra (ProgramAlgebra := MAlg T') (fun ft' => rec (f ft')) ft
    }.
