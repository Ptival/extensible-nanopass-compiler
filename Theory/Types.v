From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     ProofAlgebra
     UniversalProperty
.

(** [TypeFix] is just an alias for [UniversalPropertyF], but it makes it so that
    code that depends on wrapping types can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition TypeFix T `{FunctorLaws T}
  := UniversalPropertyF T.

Definition TypeOfResult
           T `{FunctorLaws T}
  := option (TypeFix T).

Variant ForTypeOf := .

Definition typeOf
           {E T}
           `{FunctorLaws E} `{FunctorLaws T}
           {TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
  : Fix E -> TypeOfResult T
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ _ TypeOf__E).

Definition TypeEqualityResult
           T `{FunctorLaws T}
  := TypeFix T -> bool.

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
