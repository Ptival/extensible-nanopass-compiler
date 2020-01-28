From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

(** [TypeFix] is just an alias for [UniversalPropertyF], but it makes it so that
    code that depends on wrapping types can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition TypeFix LT `{FunctorLaws LT}
  := UniversalPropertyF LT.

Definition TypeOfResult
           LT `{FunctorLaws LT}
  := option (TypeFix LT).

Variant ForTypeOf := .

Definition typeOf
           {L LT}
           `{FunctorLaws L} `{FunctorLaws LT}
           {TypeOfL : forall T, ProgramAlgebra ForTypeOf L T (TypeOfResult LT)}
  : Fix L -> TypeOfResult LT
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ _ (TypeOfL _)).

Definition TypeEqualityResult
           LT `{FunctorLaws LT}
  := TypeFix LT -> bool.

Variant ForTypeEquality := .

Definition typeEquality
           {T} `{FunctorLaws T}
           {typeEqualityForT :
              forall R,
                ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
  : Fix T -> TypeEqualityResult T
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ _ (typeEqualityForT _)).

Definition typeEqualityCorrectnessStatement
           {T} `{FunctorLaws T}
           {typeEqualityForT :
              forall R,
                ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
           (tau : Fix T)
           (UP'__tau : Fold__UP' tau)
  : Prop
  := forall tau',
    typeEquality tau tau' = true ->
    tau = proj1_sig tau'.

Variant ForTypeEqualityCorrectness := .

Lemma typeEqualityCorrectness
      {T} `{FunctorLaws T}
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
