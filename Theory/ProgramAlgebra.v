From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     SubFunctor
     Sum1
     UniversalProperty
.

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

Global Instance ProgramAlgebraLeft
       Label F G
       `{FunctorLaws F}
       `{FunctorLaws G}
  : forall {R}, ProgramAlgebra Label F R (WellFormedValue (F + G))
  := fun _ =>
    {|
      programAlgebra :=
        fun rec v => wrapUP' (inl1 (fmap rec v))
      ;
    |}.

Global Instance ProgramAlgebraRight
       Label F G
       `{FunctorLaws F}
       `{FunctorLaws G}
  : forall {R}, ProgramAlgebra Label G R (WellFormedValue (F + G))
  := fun _ =>
    {|
      programAlgebra :=
        fun rec v => wrapUP' (inr1 (fmap rec v))
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

(* Corresponds to [WFFAlgebra] *)
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
       {Label F G H T A}
       `{FAlg : ProgramAlgebra Label F T A}
       `{GAlg : ProgramAlgebra Label G T A}
       {S : SubFunctor F G}
       `{HAlg : ProgramAlgebra Label H T A}
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
       {Label F G H T A}
       `{FAlg : ProgramAlgebra Label F T A}
       `{GAlg : ProgramAlgebra Label G T A}
       `{HAlg : ProgramAlgebra Label H T A}
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
      (alg : forall T, ProgramAlgebra Label F T A)
  :=
    {
      wellFormedMendlerAlgebra (* cf. [wf_malgebra] *)
      : forall (T T' : Set) (f : T' -> T) (rec : T -> A) (ft : F T'),
        programAlgebra (ProgramAlgebra := alg T) rec (fmap f ft) =
        programAlgebra (ProgramAlgebra := alg T') (fun ft' => rec (f ft')) ft
    }.

Global Instance
       WellFormedMendlerAlgebraSum1 (* cf. [WF_Malgebra_Plus] *)
       {Label F G A}
       `{FunctorLaws F} `{FunctorLaws G}
       `{alg__F : ! forall {R}, ProgramAlgebra Label F R A}
       `{alg__G : ! forall {R}, ProgramAlgebra Label G R A}
       `{! WellFormedMendlerAlgebra (@alg__F)}
       `{! WellFormedMendlerAlgebra (@alg__G)}
  : WellFormedMendlerAlgebra (F := F + G) (fun _ => ProgramAlgebraSum1 Label F G).
Proof.
  constructor.
  move => T T' f rec [].
  - apply wellFormedMendlerAlgebra.
  - apply wellFormedMendlerAlgebra.
Qed.

Global Instance
       WellFormedMendlerAlgebra_Left
       {Label F G A}
       `{FunctorLaws F} `{FunctorLaws G}
       `{alg__F : ! forall {R}, ProgramAlgebra Label F R A}
       `{alg__G : ! forall {R}, ProgramAlgebra Label G R A}
       `{! WellFormedMendlerAlgebra (@alg__F)}
       `{! WellFormedMendlerAlgebra (@alg__G)}
  : WellFormedMendlerAlgebra (fun _ => ProgramAlgebraLeft Label F G).
Proof.
  constructor.
  move => T T' f rec ft.
  rewrite / programAlgebra / ProgramAlgebraLeft.
  rewrite fmapFusion //.
Qed.

Global Instance
       WellFormedMendlerAlgebra_Right
       {Label F G A}
       `{FunctorLaws F} `{FunctorLaws G}
       `{alg__F : ! forall {R}, ProgramAlgebra Label F R A}
       `{alg__G : ! forall {R}, ProgramAlgebra Label G R A}
       `{! WellFormedMendlerAlgebra (@alg__F)}
       `{! WellFormedMendlerAlgebra (@alg__G)}
  : WellFormedMendlerAlgebra (fun _ => ProgramAlgebraRight Label F G).
Proof.
  constructor.
  move => T T' f rec ft.
  rewrite / programAlgebra / ProgramAlgebraRight.
  rewrite fmapFusion //.
Qed.
