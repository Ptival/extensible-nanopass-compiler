From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Hacks Require Import
     TypeClassResolutionForHave
.

From ExtensibleCompiler.Semantics Require Import
     Dynamic.Eval.If2
     Static.TypeEquality
     Static.TypeEqualityCorrectness
     Static.TypeOf
     Static.TypeOf.If2
     Static.WellTyped.Bool
     Static.WellTyped.If2
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Bool
     Terms.If2
     Terms.Stuck
     Types.BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedProofAlgebra
     IndexedSubFunctor
     ProgramAlgebra
     ProofAlgebra
     SubFunctor
     Types
     TypeSoundness
     UniversalProperty
.

Local Open Scope SubFunctor.

Section If2.

  Context

    {V}
    `{Functor V}
    `{! V supports Bool}
    `{! V supports Stuck}

    {T}
    `{Functor T}
    `{! T supports BoolType}

    {E}
    `{Functor E}
    `{! E supports If2}

    {typeEqualityForT : forall R, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
  .

  Lemma Soundness__if2

        (WTV : (TypedExpr T V)-indexedPropFunctor)
        `(IndexedFunctor (TypedExpr T V) WTV)
        `((WellTypedValue__Bool <= WTV)%IndexedSubFunctor)

        `{! forall {R}, ProgramAlgebra    ForEval E R (EvalResult V)}

        (Eval__R : Set)
        {F} `{Functor F} `{F supports If2}
        recEval

        (TypeOf__R : Set)
        recTypeOf

        `{PA__TEC :
            ! ProofAlgebra ForTypeEqualityCorrectness T
              (sig (UniversalPropertyP typeEqualityCorrectnessStatement))}
        `{! WellFormedProofAlgebra PA__TEC }

        `{! IndexedProofAlgebra ForWellTypedValueProjection__Bool WTV
            (WellTypedValueProjectionStatement__Bool WTV)}
        `{! IndexedProofAlgebra ForWellTypedProj1Type WTV
            (PropertyStatement__WellTypedProj1Type WTV)
         }

    : forall Gamma (c t e : TypeOf__R) (c' t' e' : Eval__R),

      (forall tau,
          recTypeOf c = Some tau ->
          WellTyped WTV tau (recEval c' Gamma)
      ) ->

      (forall tau,
          recTypeOf t = Some tau ->
          WellTyped WTV tau (recEval t' Gamma)
      ) ->

      (forall tau,
          recTypeOf e = Some tau ->
          WellTyped WTV tau (recEval e' Gamma)
      ) ->

      forall tau,
        typeOf__If2 TypeOf__R recTypeOf (MkIf2 c t e) = Some tau ->
        WellTyped WTV tau
                  (eval__If2 Eval__R recEval (MkIf2 c' t' e') Gamma).
  Proof.
    rewrite /=.
    move => Gamma c t e c' t' e'.
    case TO__c : (recTypeOf c) => [ tau__c | ] // IH__c.
    move : IH__c (IH__c _ eq_refl) => _ WT__c.
    case BT : (isBoolType (proj1_sig tau__c)) => //.
    case TO__t : (recTypeOf t) => [ [ tau__t UP'__tau__t ] | ] // IH__t.
    move : IH__t (IH__t _ eq_refl) => _ WT__t.
    case TO__e : (recTypeOf e) => [ tau__e | ] // IH__e.
    move : IH__e (IH__e _ eq_refl) => _ WT__e.
    move => tau.
    case TE : (typeEquality tau__t tau__e) => //.
    move => [] <-.
    move : BT.
    rewrite / isBoolType.
    case p__c : (projectUP' (proj1_sig tau__c)) => [ [] | ] // _.
    {
      have := (project_successUP' _ _ (proj2_sig tau__c) p__c) => {}p__c.
      have := !! wellTypedValueProjection__Bool _ _ WT__c p__c.
      elim / @WellTypedValueInversionClear__Bool => _ _ b [] -> -> -> _.
      rewrite / isBoolean / projectUP' / if2F' / if2 /=.
      rewrite unwrapUP'_wrapF.
      rewrite wellFormedSubFunctor.
      rewrite wellFormedSubFunctor.
      rewrite project_inject /=.
      move : b => [].
      {
        apply WT__t.
      }
      {
        have := !! typeEqualityCorrectness (exist _ _ _) _ TE => TEC.
        have := !! wellTypedProj1Type _ _ WT__e _ UP'__tau__t TEC => //.
      }
    }
  Defined.

  Global Instance Soundness__If2

         (WTV : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WTV)
         `((WellTypedValue__Bool  <= WTV)%IndexedSubFunctor)

         `{! forall {R}, ProgramAlgebra
                      ForEval E R (EvalResult V)}
         `{! forall {R}, WellFormedCompoundProgramAlgebra
                      ForEval E If2 R (EvalResult V)}

         (recEval : WellFormedValue E -> EvalResult   V)

         `{! forall {R}, ProgramAlgebra
                      ForTypeOf E     R (TypeOfResult T)}
         `{! forall {R}, WellFormedCompoundProgramAlgebra
                      ForTypeOf E If2 R (TypeOfResult T)}
         (recTypeOf : WellFormedValue E -> TypeOfResult T)

        `{PA__TEC :
            ! ProofAlgebra ForTypeEqualityCorrectness T
              (sig (UniversalPropertyP typeEqualityCorrectnessStatement))}
        `{! WellFormedProofAlgebra PA__TEC}

        `{! IndexedProofAlgebra ForWellTypedValueProjection__Bool WTV
            (WellTypedValueProjectionStatement__Bool WTV)}

        `{! IndexedProofAlgebra ForWellTypedProj1Type WTV
            (PropertyStatement__WellTypedProj1Type WTV)
         }

    : ProofAlgebra
        ForSoundness If2
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WTV recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2__If2.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    move => [c1 c2] [t1 t2] [e1 e2] /=.
    move => [[UP'__c1 UP'__c2] IH__c] [[UP'__t1 UP'__t2] IH__t] [[UP'__e1 UP'__e2] IH__e].
    constructor.
    {
      apply conj; exact (proj2_sig (if2 _ _ _)).
    }
    {
      move => Gamma.
      rewrite / if2F' / if2F / if2 / inject /=.
      rewrite !unwrapUP'_wrapF /=.
      rewrite !fmapFusion /=.
      rewrite / Extras.compose /=.
      rewrite !wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      rewrite ! wellFormedCompoundProgramAlgebra.
      move => IH tau.
      eapply Soundness__if2 => //.

      (* condition *)
      {
        move => ?.
        apply (IH Gamma (exist _ _ UP'__c1, _)) => /=.
        {
          move => A B.
          apply (IH__c Gamma IH).
          now rewrite <- (wrapUP'_unwrapUP' c2).
        }
      }

      (* then branch *)
      {
        move => ?.
        apply (IH Gamma (exist _ _ UP'__t1, _)) => /=.
        {
          move => A B.
          apply (IH__t Gamma IH).
          now rewrite <- (wrapUP'_unwrapUP' t2).
        }
      }

      (* else branch *)
      {
        move => ?.
        apply (IH Gamma (exist _ _ UP'__e1, _)) => /=.
        {
          move => A B.
          apply (IH__e Gamma IH).
          now rewrite <- (wrapUP'_unwrapUP' e2).
        }
      }

    }
  Defined.

End If2.
