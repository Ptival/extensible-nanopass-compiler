From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import

     Semantics.All.Bool
     Semantics.All.BoolType
     Semantics.All.If2
     Semantics.Static.TypeOf

     Syntax.Terms.Bool
     Syntax.Terms.If2
     Syntax.Terms.Stuck
     Syntax.Types.BoolType

     Theory.Algebra
     Theory.Eval
     Theory.IndexedAlgebra
     Theory.IndexedFunctor
     Theory.IndexedProofAlgebra
     Theory.IndexedSubFunctor
     Theory.IndexedSum1
     Theory.ProgramAlgebra
     Theory.ProofAlgebra
     Theory.Sum1
     Theory.Types
     Theory.TypeSoundness
     Theory.UniversalProperty

.

Definition T := BoolType.

Definition E := (Bool + If2)%Sum1.

Definition V := (Bool + Stuck)%Sum1.

Definition WTV
  : (TypedValue T V)-indexedPropFunctor
  := WellTypedValue__Bool.

Definition eval'
  : WellFormedValue E -> EvalResult V
  := fun v => eval (proj1_sig v).

Definition typeOf'
  : WellFormedValue E -> TypeOfResult T
  := fun v => typeOf (proj1_sig v).

Definition Soundness__WTV
  : Soundness__ProofAlgebra (T := T) (E := E) (V := V) WTV.
Proof.
  move => recEval recTypeOf.
  apply ProofAlgebra__Sum1.
  apply (
      Soundness__Bool
        WTV _ _ recEval recTypeOf
    ).
  apply (
      Soundness__If2
        WTV _ _ recEval recTypeOf
    ).
Defined.

Theorem Soundness
  : forall Gamma (tau : TypeFix T) (e : WellFormedValue E),
    typeOf (proj1_sig e) = Some tau ->
    WellTyped WTV tau (eval (proj1_sig e) Gamma).
Proof.
  intros Gamma tau e.
  pose proof (proofAlgebra' (Soundness__If2 _ _ _ eval' typeOf')) as A.
  pose proof (Soundness (T := T) (E := E) (V := V) WTV Soundness__WTV) as S.
  apply : S.
  move => rE rTO.
  econstructor.
  - move => [] [] //.
  - move => [] [] //.
Qed.
