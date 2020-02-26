From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import

     Semantics.Static.TypeEquality
     Semantics.Static.TypeEquality.BoolType
     Semantics.Static.TypeEqualityCorrectness

     Syntax.Types.BoolType

     Theory.Algebra
     Theory.Eval
     Theory.Functor
     Theory.ProofAlgebra
     Theory.ProgramAlgebra
     Theory.SubFunctor
     Theory.Sum1
     Theory.Types
     Theory.UniversalProperty

.

Local Open Scope SubFunctor.

Section BoolType.

  Context
    {T}
    `{Functor T}
    `{T supports BoolType}
  .

  Global Instance TypeEqualityCorrectness__BoolType
         `{! forall {R}, ProgramAlgebra
                         ForTypeEquality T R (TypeEqualityResult T)}
         `{! forall {R}, WellFormedCompoundProgramAlgebra
                      ForTypeEquality T BoolType R (TypeEqualityResult T)}
    : ProofAlgebra
        ForTypeEqualityCorrectness
        BoolType
        (sig (UniversalPropertyP (typeEqualityCorrectnessStatement (T := T)))).
  Proof.
    constructor => [] [].
    exists boolType.
    rewrite / UniversalPropertyP.
    econstructor.
    rewrite / typeEqualityCorrectnessStatement.
    move => tau'.
    rewrite / typeEquality / mendlerFold {1} / boolType / boolType'.
    rewrite {1} / injectUP' /=.
    rewrite {1} wellFormedSubFunctor /=.
    rewrite {1} / wrapF.
    rewrite wellFormedCompoundProgramAlgebra /=.
    rewrite / isBoolType.
    case P : (projectUP' (proj1_sig tau')) => [ [] | ] // => _.
    move : P.
    rewrite / projectUP'.
    move => P.
    move : P (project_success P) => _.
    rewrite / boolType / boolType' /=.
    rewrite wellFormedSubFunctor /=.
    move => P.
    move : P (f_equal wrapUP' P) => _.
    move => P.
    move : P (f_equal (@proj1_sig _ _) P) => _.
    setoid_rewrite wrapUP'_unwrapUP'.
    {
      move => -> /=.
      rewrite wellFormedSubFunctor //.
    }
    {
      apply proj2_sig.
    }
  Defined.

  Global Instance WellFormedProofAlgebra__TypeEqualityCorrectness__BoolType
         `{! forall {R}, ProgramAlgebra
                      ForTypeEquality T R (TypeEqualityResult T)}
         `{! forall {R}, WellFormedCompoundProgramAlgebra
                      ForTypeEquality T BoolType R (TypeEqualityResult T)}
    : WellFormedProofAlgebra TypeEqualityCorrectness__BoolType.
  Proof.
    constructor.
    move => [] /=.
    rewrite / boolType / boolType' /=.
    now rewrite wellFormedSubFunctor.
  Qed.

End BoolType.
