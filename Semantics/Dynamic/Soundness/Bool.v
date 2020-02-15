From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Semantics Require Import
     Dynamic.Eval.Bool
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
         `((WellTypedValue__Bool <= WT)%IndexedSubFunctor)

         `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{! forall {R}, WellFormedProgramAlgebra Eval__Bool Eval__E (T := R)}
         (recEval   : WellFormedValue E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__Bool TypeOf__E (T := R)}
         (recTypeOf : WellFormedValue E -> TypeOfResult T)

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
      apply (iInject (F := WellTypedValue__Bool)) => /=.
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
  : Soundness__ProofAlgebra (T := T) (E := Bool) (V := V) WellTypedValue__Bool.
Proof.
  move => recEval recTypeOf.
  apply : Soundness__Bool.
Qed.
