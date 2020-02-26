From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Semantics.Static Require Import
     TypeEquality
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     ProofAlgebra
     Types
     UniversalProperty
.

Definition typeEqualityCorrectnessStatement
           {T} `{Functor T}
           {TypeEquality__T :
              forall {R},
                ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
           (tau : Fix T)
           (UP'__tau : FoldUP' tau)
  : Prop
  := forall tau',
    typeEquality tau tau' = true ->
    tau = proj1_sig tau'.

Variant ForTypeEqualityCorrectness := .

Lemma typeEqualityCorrectness
      {T} `{Functor T}
      {typeEqualityForT :
         forall R,
           ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
      `{PA : ! ProofAlgebra ForTypeEqualityCorrectness T
                     (sig (UniversalPropertyP typeEqualityCorrectnessStatement))}
      `{! WellFormedProofAlgebra PA}
  : forall tau, typeEqualityCorrectnessStatement (proj1_sig tau) (proj2_sig tau).
Proof.
  move => tau.
  apply (
      proj2_sig
        (Induction
           (P := UniversalPropertyP typeEqualityCorrectnessStatement)
           _
           (proj2_sig tau)
        )
    ).
Qed.
