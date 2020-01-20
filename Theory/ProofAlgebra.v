From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

(**

[ProofAlgebra] captures those algebras that we will use for theorem proving.
Because proofs are not computationally-revelant, they will never use more
advanced algebras like Mendler of Mixin.  Simple, plain old algebras suffice.

In practice, we will use them at type [sig P] for a given property [P] to prove
about the term of interest.

*)

Class ProofAlgebra F `{Functor F} A :=
  {
    proofAlgebra : Algebra F A;
  }.

Global Instance
       ProofAlgebraSum1
       {A}
       {F} `{Functor F} (FAlg : ProofAlgebra F A)
       {G} `{Functor G} (GAlg : ProofAlgebra G A)
  : ProofAlgebra (F + G) A
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
                           wrapFix

*)

(* Corresponds to [WF__Ind] *)
(** NOTE: it does not pay off trying to make this be about [WellFormedValue]
    properties, because we will not be able to prove the property over the
    dependent pair, only about its [proj1_sig].
*)
Class WellFormedProofAlgebra
      {F G} `{Functor F} `{FunctorLaws G} `{FG : F <= G}
      {P : Fix G -> Prop} (PA : ProofAlgebra F (sig P))
  :=
    {
      projEq
      : forall e,
        (* run [proofAlgebra], then observe the term *)
        proj1_sig (proofAlgebra (ProofAlgebra := PA) e)
        =
        (* observe all subterms via [fmap], and combine them *)
        wrapFix (inj (SubFunctor := FG) (fmap (proj1_sig (P := P)) e));
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
      {F} `{Functor F}
      `{FunctorLaws F}
      e {RFUP : ReverseFoldUniversalProperty e}
      (A B : Set) (h : A -> B) (f : Algebra F A) (g : Algebra F B)
      (HF : forall a, h (f a) = g (fmap h a))
      : (fun e' => h (fold f e')) e = fold g e.
Proof.
  apply elimFoldUniversalProperty.
  intros e'.
  rewrite (DirectFoldUniversalProperty F _ f).
  {
    rewrite HF.
    rewrite fmapFusion.
    unfold Extras.compose.
    reflexivity.
  }
  { reflexivity. }
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

Lemma Induction
      {F} `{Functor F} `{FunctorLaws F}
      {P : Fix F -> Prop}
      {PA : ProofAlgebra F (sig P)}
      {WFPA : WellFormedProofAlgebra PA}
  : forall (f : Fix F), ReverseFoldUniversalProperty f -> P f.
Proof.
  intros f UP.
  cut (proj1_sig (fold (@proofAlgebra _ _ _ PA) f) = id f).
  {
    intro FEQ.
    unfold id in FEQ.
    rewrite <- FEQ.
    eapply proj2_sig.
  }
  {
    erewrite Fusion'.
    {
      now rewrite foldWrapFixIdentity.
    }
    {
      assumption.
    }
    {
      intros.
      rewrite projEq.
      simpl.
      reflexivity.
    }
  }
Qed.

Lemma Induction'
      {F} `{Functor F} `{FunctorLaws F}
      {P : Fix F -> Prop}
      {PA : ProofAlgebra F (sig P)}
      {WFPA : WellFormedProofAlgebra PA}
  : forall (f : WellFormedValue F), P (proj1_sig f).
Proof.
  destruct f as [f UP].
  now apply Induction.
Qed.
