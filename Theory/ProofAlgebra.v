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

[ProofAlgebra] captures those algebras that we will use for theorem proving.
Because proofs are not computationally-revelant, they will never use more
advanced algebras like Mendler of Mixin.  Simple, plain old algebras suffice.

In practice, we will use them at type [sig P] for a given property [P] to prove
about the term of interest.

In order to distinguish some [ProofAlgebra]s that would otherwise have the
same signature, each [ProofAlgebra] is given a unique [Label].  This helps
the typeclass mechanism find the appropriate instance among a bunch of program
algebras with the same carrier types.

You can just create a new label with:
[Variant MyLabel := .]
The type does not need any inhabitant, we only use its type identity.

*)

Class ProofAlgebra (* cf. [PAlgebra] *)
      (Label : Set) F `{Functor F} A :=
  {
    proofAlgebra (* cf. [p_algebra] *)
    : Algebra F A;
  }.

(**
Just like [proofAlgebra], but when you want to provide the [ProofAlgebra]
explicitly.
 *)
Definition proofAlgebra'
           {Label F A}
           `{FunctorLaws F}
           (PA : ProofAlgebra Label F A)
  : Algebra F A
  := proofAlgebra (ProofAlgebra := PA).

Global Instance
       ProofAlgebraSum1
       {Label} F G {A}
       `{Functor F} `{Functor G}
       {FAlg : ProofAlgebra Label F A}
       {GAlg : ProofAlgebra Label G A}
  : ProofAlgebra Label (F + G) A
  :=
    {|
      proofAlgebra :=
        fun fg =>
          match fg with
          | inl1 f => proofAlgebra f
          | inr1 g => proofAlgebra g
          end
      ;
    |}.

(**

A proof-producing [ProofAlgebra] is well-formed if the term it re-creates by
applying the algebra (in the left hand of the dependent pair) is indeed the
original term.  That is, the following diagram commutes:

                          proofAlgebra
F (Σ (e : Fix G) . P e) ---------------> Σ (e : Fix G) . P e
        |                                          |
        | fmap proj1_sig                           |
        v                                          |
     F (Fix G)                                     | proj1_sig
        |                                          |
        | inj                                      |
        v                                          v
    G (Fix G) ---------------------------------> Fix G
                           wrapF

*)

(** NOTE: it does not pay off trying to make this be about [WellFormedValue]
    properties, because we will not be able to prove the property over the
    dependent pair, only about its [proj1_sig].
*)
Class WellFormedProofAlgebra (* cf. [WF_Ind] *)
      {Label F G}
      `{S : SubFunctor F G}
      {P : Fix G -> Prop} `(PA : ! ProofAlgebra Label F (sig P))
  :=
    {
      projEq
      : forall e,
        (* run [proofAlgebra], then observe the term *)
        proj1_sig (proofAlgebra (ProofAlgebra := PA) e)
        =
        (* observe all subterms via [fmap], and combine them *)
        wrapF (inj (SubFunctor := S) (fmap (proj1_sig (P := P)) e));
    }.

(** TODO: document why we need this *)
Class WellFormedProofAlgebra2 (* cf. [WF_Ind2] *)
      {Label F G H}
      `{SG : SubFunctor F G} `{SH : SubFunctor F H}
      {P : (Fix G * Fix H) -> Prop} `(PA : ! ProofAlgebra Label F (sig P))
  :=
    {
      proj1Eq
      : forall e,
        (* run [proofAlgebra], then observe the term *)
        fst (proj1_sig (proofAlgebra (ProofAlgebra := PA) e))
        =
        (* observe all subterms via [fmap], and combine them *)
        wrapF (inj (SubFunctor := SG) (fmap (fun e => fst (proj1_sig (P := P) e)) e));
      proj2Eq
      : forall e,
        (* run [proofAlgebra], then observe the term *)
        snd (proj1_sig (proofAlgebra (ProofAlgebra := PA) e))
        =
        (* observe all subterms via [fmap], and combine them *)
        wrapF (inj (SubFunctor := SH) (fmap (fun e => snd (proj1_sig (P := P) e)) e));
    }.

(* TODO *)
(*
Global Instance
       WellFormedProofAlgebraSum1
       {P}
       {F} `{Functor F} {FAlg : ProofAlgebra F (sig P)}
       {G} `{Functor G} {GAlg : ProofAlgebra G (sig P)}
       {H} `{Functor H}
       `{FGH : (F + G) <= H}
       {_ : WellFormedProofAlgebra (F := F) (G := H) (FG := SubFunctorLeft  (FG := FGH)) FAlg}
       {_ : WellFormedProofAlgebra (F := G) (G := H) (FG := SubFunctorRight (FH := FGH)) GAlg}
  : WellFormedProofAlgebra (ProofAlgebraSum1 FAlg GAlg).
Proof.
  constructor.
  intros rec f.
  unfold inj.
  unfold SubFunctorLeft.
  simpl.
  rewrite wellFormedProofAlgebra.
  reflexivity.
Qed.
 *)

Lemma Fusion'
      {F} `{FunctorLaws F}
      (e : Fix F) {UP : FoldUP' e}
      (A B : Set) (h : A -> B) (f : Algebra F A) (g : Algebra F B)
      (HF : forall a, h (f a) = g (fmap h a))
      : (fun e' => h (fold f e')) e = fold g e.
Proof.
  apply foldUP'.
  intros e'.
  rewrite (FoldUP F _ f).
  { reflexivity. }
  {
    rewrite HF.
    rewrite fmapFusion.
    unfold Extras.compose.
    reflexivity.
  }
Qed.

Lemma Fusion
      {F} `{Functor F}
      `{FunctorLaws F}
      (e : WellFormedValue F)
      (A B : Set) (h : A -> B) (f : Algebra F A) (g : Algebra F B)
      (HF : forall a, h (f a) = g (fmap h a))
      : (fun e' => h (fold f e')) (proj1_sig e) = fold g (proj1_sig e).
Proof.
  destruct e; now apply Fusion'.
Qed.

Lemma proj1_fold_is_id
      {Label F} `{FunctorLaws F}
      {P : Fix F -> Prop}
      {PA : ProofAlgebra Label F (sig P)}
      {WFPA : WellFormedProofAlgebra PA}
  : forall (f : Fix F),
    FoldUP' f ->
    proj1_sig (fold (proofAlgebra' PA) f) = f.
Proof.
  move => f UP.
  setoid_rewrite Fusion' with (g := wrapF) => //.
  {
    rewrite fold_wrapF_Identity //.
  }
  {
    move => a.
    rewrite projEq //.
  }
Qed.

Lemma fst_proj1_fold_is_id
      {Label F} `{FunctorLaws F}
      {P : (Fix F * Fix F) -> Prop}
      {PA : ProofAlgebra Label F (sig P)}
      {WFPA : WellFormedProofAlgebra2 PA}
  : forall (f : Fix F),
    FoldUP' f ->
    fst (proj1_sig (fold (proofAlgebra' PA) f)) = f.
Proof.
  move => f UP.
  setoid_rewrite (Fusion' f _ _ (fun e => fst (proj1_sig e)) _ wrapF).
  {
    rewrite fold_wrapF_Identity //.
  }
  {
    move => a.
    rewrite proj1Eq //.
  }
Qed.

Lemma snd_proj1_fold_is_id
      {Label F} `{FunctorLaws F}
      {P : (Fix F * Fix F) -> Prop}
      {PA : ProofAlgebra Label F (sig P)}
      {_ : WellFormedProofAlgebra2 PA}
  : forall (f : Fix F),
    FoldUP' f ->
    snd (proj1_sig (fold (proofAlgebra' PA) f)) = f.
Proof.
  move => f UP.
  setoid_rewrite (Fusion' f _ _ (fun e => snd (proj1_sig e)) _ wrapF).
  {
    rewrite fold_wrapF_Identity //.
  }
  {
    move => a.
    rewrite proj2Eq //.
  }
Qed.

Lemma Induction (* cf. [Ind] *)
      {Label F} `{FunctorLaws F}
      {P : Fix F -> Prop}
      {PA : ProofAlgebra Label F (sig P)}
      {_ : WellFormedProofAlgebra PA}
  : forall (f : Fix F),
    FoldUP' f ->
    P f.
Proof.
  move => f UP.
  setoid_rewrite <- proj1_fold_is_id => //.
  apply proj2_sig.
Qed.

Lemma Induction'
      {Label F} `{Functor F} `{FunctorLaws F}
      {P : Fix F -> Prop}
      {PA : ProofAlgebra Label F (sig P)}
      {_ : WellFormedProofAlgebra PA}
  : forall (f : WellFormedValue F), P (proj1_sig f).
Proof.
  destruct f as [f UP].
  now apply Induction.
Qed.

Lemma Induction2 (* cf. [Ind2] *)
      {Label F} `{FunctorLaws F}
      {P : (Fix F * Fix F) -> Prop}
      {PA : ProofAlgebra Label F (sig P)}
      {_ : WellFormedProofAlgebra2 PA}
  : forall (f : Fix F),
    FoldUP' f ->
    P (f, f).
Proof.
  move => f UP.
  setoid_rewrite <- (fst_proj1_fold_is_id f UP) at 1.
  setoid_rewrite <- (snd_proj1_fold_is_id f UP) at 2.
  rewrite <- surjective_pairing.
  apply proj2_sig.
Qed.
