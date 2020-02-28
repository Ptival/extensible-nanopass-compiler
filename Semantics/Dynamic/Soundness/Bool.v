From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Semantics Require Import
     Dynamic.Eval.Bool
     Static.TypeOf
     Static.TypeOf.Bool
     Static.WellTyped.Bool
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Bool
     Types.BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     ProofAlgebra
     ProgramAlgebra
     SubFunctor
     Types
     TypeSoundness
     UniversalProperty
.

Local Open Scope SubFunctor.

Section Bool.

  Context
    {V}
    `{Functor V}
    `{! V supports Bool}

    {E}
    `{Functor E}
    `{! E supports Bool}

    {T}
    `{Functor T}
    `{! T supports BoolType}
  .

  Global Instance Soundness__Bool

         (WTV : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WTV)
         `((WellTypedValue__Bool <= WTV)%IndexedSubFunctor)

         `{Eval__E : ! forall R, ProgramAlgebra ForEval E R (EvalResult V)}
         `{! forall R, WellFormedCompoundProgramAlgebra (Eval__E R) Eval__Bool}

         (recEval   : WellFormedValue E -> EvalResult V)

         `{TypeOf__E : ! forall R, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall R, WellFormedCompoundProgramAlgebra (TypeOf__E R) TypeOf__Bool}

         (recTypeOf : WellFormedValue E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness Bool
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WTV recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2Algebra__Bool => b.
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
      rewrite wellFormedCompoundProgramAlgebra.
      rewrite wellFormedCompoundProgramAlgebra.
      move => IH tau TY.
      apply (iInject (F := WellTypedValue__Bool)) => /=.
      econstructor => //.
      move : TY => /=.
      move => [] <- //.
    }
  Defined.

End Bool.
