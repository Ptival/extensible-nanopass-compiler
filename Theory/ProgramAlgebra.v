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

Class ProgramAlgebra F `{Functor F} T A :=
  {
    programAlgebra : MixinAlgebra T F A;
  }.

Global Instance
       ProgramAlgebraSum1
       {T A}
       {F} `{Functor F} (FAlg : ProgramAlgebra F T A)
       {G} `{Functor G} (GAlg : ProgramAlgebra G T A)
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
Class WellFormedProgramAlgebra
      {T A F G} `{Functor F} `{Functor G} `{FG : F <= G}
      (FAlg : ProgramAlgebra F T A)
      (GAlg : ProgramAlgebra G T A)
  :=
    {
      wellFormedProgramAlgebra
      : forall rec (fa : F T),
        @programAlgebra G _ _ _ _ rec (inj (SubFunctor := FG) fa)
        =
        @programAlgebra F _ _ _ _ rec fa;
    }.

Global Instance
       WellFormedProgramAlgebraRefl
       {F} `{Functor F}
       {T A} {FAlg : ProgramAlgebra F T A}
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
       {T A}
       {F} `{Functor F} {FAlg : ProgramAlgebra F T A}
       {G} `{Functor G} {GAlg : ProgramAlgebra G T A}
       {H} `{Functor H} {HAlg : ProgramAlgebra H T A}
       {FG : F <= G}
       {WFFG : WellFormedProgramAlgebra FAlg GAlg}
  : WellFormedProgramAlgebra FAlg (ProgramAlgebraSum1 GAlg HAlg).
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
       {T A}
       {F} `{Functor F} {FAlg : ProgramAlgebra F T A}
       {G} `{Functor G} {GAlg : ProgramAlgebra G T A}
       {H} `{Functor H} {HAlg : ProgramAlgebra H T A}
       {FH : F <= H}
       {WFFH : WellFormedProgramAlgebra FAlg HAlg}
  : WellFormedProgramAlgebra FAlg (ProgramAlgebraSum1 GAlg HAlg).
Proof.
  constructor.
  intros rec f.
  unfold inj.
  unfold SubFunctorRight.
  simpl.
  rewrite wellFormedProgramAlgebra.
  reflexivity.
Qed.
