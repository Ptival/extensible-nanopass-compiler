From Coq Require Import ssreflect.

From ExtensibleCompiler Require Import

     Semantics.Dynamic.Eval.Bool
     Semantics.Static.TypeOf.Bool
     Semantics.Static.WellTyped.Bool

     Syntax.Terms.Bool
     Syntax.Types.BoolType

     Theory.Algebra
     Theory.Eval
     Theory.Functor
     Theory.IndexedAlgebra
     Theory.IndexedFunctor
     Theory.IndexedSubFunctor
     Theory.ProofAlgebra
     Theory.ProgramAlgebra
     Theory.SubFunctor
     Theory.Types
     Theory.TypeSoundness
     Theory.UniversalProperty

.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}

    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
    `{! WellFormedSubFunctor Bool E}

    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
  .

  Global Instance Soundness__Bool

         (WT : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WT)
         `((WellTyped__Bool <= WT)%IndexedSubFunctor)

         `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{! forall {R}, WellFormedProgramAlgebra Eval__Bool Eval__E (T := R)}
         (recEval   : UniversalPropertyF E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__Bool TypeOf__E (T := R)}
         (recTypeOf : UniversalPropertyF E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness Bool
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WT recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2Algebra_Bool => b.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    constructor.
    {
      apply conj; apply (proj2_sig (boolean b)).
    }
    {
      move => Gamma.
      rewrite / booleanF / boolean / inject /=.
      rewrite unwrapUP'_wrapF /=.
      rewrite fmapFusion / Extras.compose /=.
      rewrite wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      rewrite wellFormedProgramAlgebra.
      rewrite wellFormedProgramAlgebra.
      move => IH tau TY.
      apply (iInject (F := WellTyped__Bool)) => /=.
      econstructor => //.
      move : TY => /=.
      move => [] <- //.
    }
  Qed.

End Bool.

(* small sanity check *)
Definition Soundness__Bool'
           {V}
           `{FunctorLaws V}
           `{! V supports Bool}
           {T}
           `{FunctorLaws T}
           `{! T supports BoolType}
  : Soundness__ProofAlgebra (T := T) (E := Bool) (V := V) WellTyped__Bool.
Proof.
  move => recEval recTypeOf.
  apply : Soundness__Bool.
Qed.
