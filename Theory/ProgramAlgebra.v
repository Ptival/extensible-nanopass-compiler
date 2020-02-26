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

Local Open Scope SubFunctor.
Local Open Scope Sum1.

(**

[ProgramAlgebra] captures those algebras that we will use for programming.
Because programs are computationally-revelant, we need [MixinAlgebra]s.

In order to distinguish some [ProgramAlgebra]s that would otherwise have the
same signature, each [ProgramAlgebra] is given a unique [Tag].  This helps
the typeclass mechanism find the appropriate instance among a bunch of program
algebras with the same carrier types.

You can just create a new label with:
[Variant MyTag := .]
The type does not need any inhabitant, we only use its type identity.

 *)
Class ProgramAlgebra (* cf. [FAlgebra] *)
      (Tag : Set) F T A
      `{Functor F}
  :=
    {
      programAlgebra : (* cf. [f_algebra] *)
        MixinAlgebra F T A;
    }.

(**
Just like [programAlgebra], but when you want to provide the [ProgramAlgebra]
explicitly.
 *)
Definition programAlgebra'
           {Tag F T A}
           `{Functor F}
           (PA : ProgramAlgebra Tag F T A)
  := programAlgebra (ProgramAlgebra := PA).

(**
A version of [mendlerFold] specialized to handling [ProgramAlgebra]s.
Convenient to use because you can explicitly pass the algebra.
 *)
Definition foldProgramAlgebra
           {Tag F O}
           `{Functor F}
           `{Alg : ! forall {T}, ProgramAlgebra Tag F T O}
           (e : Fix F)
  : O
  := mendlerFold (fun _ => programAlgebra' Alg) e.

Global Instance
       ProgramAlgebra__Sum1 Tag F G {T A}
       `{ProgramAlgebra Tag F T A}
       `{ProgramAlgebra Tag G T A}
  : ProgramAlgebra Tag (F + G) T A
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

Global Instance ProgramAlgebra__Left
       Tag F G
       `{Functor F}
       `{Functor G}
  : forall {R}, ProgramAlgebra Tag F R (WellFormedValue (F + G))
  := fun _ =>
    {|
      programAlgebra :=
        fun rec v => wrapUP' (inl1 (fmap rec v))
      ;
    |}.

Global Instance ProgramAlgebra__Right
       Tag F G
       `{Functor F}
       `{Functor G}
  : forall {R}, ProgramAlgebra Tag G R (WellFormedValue (F + G))
  := fun _ =>
    {|
      programAlgebra :=
        fun rec v => wrapUP' (inr1 (fmap rec v))
      ;
    |}.

(**

A program-producing [ProgramAlgebra] is well-formed when it properly dispatches
to its sub-algebras.

             programAlgebra Alg__F
       F T -------------------------> A
        |                             =
        | inj                         =
        v                             =
       E T -------------------------> A
             programAlgebra Alg__E

*)

(**
NOTE: we need to specify [E := E] or the type class mechanism will pick
[SubFunctor__Refl] and inject from [F] into [F].
 *)
Class WellFormedCompoundProgramAlgebra (* cf. [WFFAlgebra] *)
      Tag E F T A
      `{Functor E} `{Functor F}
      `{E supports F}
      `{ProgramAlgebra Tag E T A}
      `{ProgramAlgebra Tag F T A}
  :=
    {
      wellFormedCompoundProgramAlgebra :
        forall rec (fa : F T),
          programAlgebra rec (inject (E := E) fa)
          =
          programAlgebra rec fa
      ;
    }.

Global Instance
       WellFormedCompoundProgramAlgebra__Refl
       {Tag F T A}
       `{ProgramAlgebra Tag F T A}
  : WellFormedCompoundProgramAlgebra Tag F F T A.
Proof.
  constructor => rec fa //.
Qed.

Global Instance
       WellFormedCompoundProgramAlgebra__Left
       {Tag F G H T A}
       `{Functor F} `{Functor G} `{Functor H}
       `{G supports F}
       `{! ProgramAlgebra Tag F T A}
       `{! ProgramAlgebra Tag G T A}
       `{! ProgramAlgebra Tag H T A}
       `{! WellFormedCompoundProgramAlgebra Tag G F T A}
  : WellFormedCompoundProgramAlgebra Tag (G + H) F T A.
Proof.
  constructor => rec f.
  rewrite /= wellFormedCompoundProgramAlgebra //.
Qed.

Global Instance
       WellFormedCompoundProgramAlgebraRight
       {Tag F G H T A}
       `{Functor F} `{Functor G} `{Functor H}
       `{H supports F}
       `{! ProgramAlgebra Tag F T A}
       `{! ProgramAlgebra Tag G T A}
       `{! ProgramAlgebra Tag H T A}
       `{! WellFormedCompoundProgramAlgebra Tag H F T A}
  : WellFormedCompoundProgramAlgebra Tag (G + H) F T A.
Proof.
  constructor => rec f.
  rewrite /= wellFormedCompoundProgramAlgebra //.
Qed.

Class WellFormedProgramAlgebra (* cf. [WF_Malgebra] *)
      Tag F A
      `{Functor F}
      `{forall T, ProgramAlgebra Tag F T A}
  :=
    {
      wellFormedProgramAlgebra : (* cf. [wf_malgebra] *)
        forall (T T' : Set) (f : T' -> T) (rec : T -> A) (ft : F T'),
          programAlgebra rec (fmap f ft)
          =
          programAlgebra (fun ft' => rec (f ft')) ft
      ;
    }.

Global Instance
       WellFormedProgramAlgebra__Sum1 (* cf. [WF_Malgebra_Plus] *)
       {Tag F G A}
       `{Functor F} `{Functor G}
       `{! forall {R}, ProgramAlgebra Tag F R A}
       `{! forall {R}, ProgramAlgebra Tag G R A}
       `{! WellFormedProgramAlgebra Tag F A}
       `{! WellFormedProgramAlgebra Tag G A}
  : WellFormedProgramAlgebra Tag (F + G) A.
Proof.
  constructor => T T' f rec [].
  - apply wellFormedProgramAlgebra.
  - apply wellFormedProgramAlgebra.
Qed.

Global Instance
       WellFormedProgramAlgebra__Left
       {Tag F G}
       `{Functor F} `{Functor G}
  : WellFormedProgramAlgebra Tag F (WellFormedValue (F + G)).
Proof.
  constructor => T T' f rec ft /=.
  rewrite fmapFusion //.
Qed.

Global Instance
       WellFormedProgramAlgebra__Right
       {Tag F G}
       `{Functor F} `{Functor G}
  : WellFormedProgramAlgebra Tag G (WellFormedValue (F + G)).
Proof.
  constructor => T T' f rec gt /=.
  rewrite fmapFusion //.
Qed.
