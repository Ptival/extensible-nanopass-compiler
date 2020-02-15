From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Hacks Require Import
     TypeClassResolutionForHave
.

From ExtensibleCompiler.Semantics Require Import
     Dynamic.Eval.If2
     Static.TypeOf.If2
     Static.WellTyped.Bool
     Static.WellTyped.If2
     Static.WellTyped.Stuck
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
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports Stuck}
    `{! WellFormedSubFunctor Bool V}
    `{! WellFormedSubFunctor Stuck V}

    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}

    {E}
    `{FunctorLaws E}
    `{! E supports If2}
    `{! WellFormedSubFunctor If2 E}

    {typeEqualityForT : forall R, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
  .

  Lemma Soundness__if2

        (WTV : (TypedExpr T V)-indexedPropFunctor)
        `(IndexedFunctor (TypedExpr T V) WTV)
        `((WellTypedValue__Bool <= WTV)%IndexedSubFunctor)
        `((WellTypedValue__Stuck <= WTV)%IndexedSubFunctor)

        `{Eval__E : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
        `{! forall {R}, WellFormedProgramAlgebra Eval__If2 Eval__E (T := R)}

        (Eval__R : Set)
        {F} `{FunctorLaws F} `{F supports If2}
        recEval

        (TypeOf__R : Set)
        recTypeOf

        `{PA__TypeEqualityCorrectness :
            ! ProofAlgebra ForTypeEqualityCorrectness T
              (sig (UniversalPropertyP typeEqualityCorrectnessStatement))}
        `{! WellFormedProofAlgebra PA__TypeEqualityCorrectness}

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
    case TO__c : (recTypeOf c) => [ tau__c | ] // H__c.
    move : H__c (H__c _ eq_refl) => _ WT__c.
    case BT : (isBoolType (proj1_sig tau__c)) => //.
    case TO__t : (recTypeOf t) => [ [ tau__t UP'__tau__t ] | ] // H__t.
    move : H__t (H__t _ eq_refl) => _ WT__t.
    case TO__e : (recTypeOf e) => [ tau__e | ] // H__e.
    move : H__e (H__e _ eq_refl) => _ WT__e.
    move => tau.
    case TE : (typeEquality tau__t tau__e) => //.
    move => [] <-.
    move : BT.
    rewrite / isBoolType.
    case p__c : (project (proj1_sig tau__c)) => [ [] | ] // _.
    {
      have := (project_inject _ _ (proj2_sig tau__c) p__c) => {}p__c.
      have := !! wellTypedValueProjection__Bool _ _ WT__c p__c.
      elim / @WellTypedValueInversionClear__Bool => _ _ b [] -> -> -> _.
      rewrite / isBoolean / project / if2F' / if2 /=.
      rewrite unwrapUP'_wrapF.
      rewrite wellFormedSubFunctor.
      rewrite wellFormedSubFunctor.
      case PI : (prj (inj _)) => [ a | ].
      {
        move : a PI => [] [] PI.
        {
          apply WT__t.
        }
        {
          have := !! typeEqualityCorrectness (exist _ _ _) _ TE => TEC.
          have := !! wellTypedProj1Type _ _ WT__e _ UP'__tau__t TEC => //.
        }
      }
      {
        apply (iInject (F := WellTypedValue__Stuck)).
        econstructor.
        reflexivity.
      }
    }
  Qed.

  Global Instance Soundness__If2

         (WTV : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WTV)
         `((WellTypedValue__Bool  <= WTV)%IndexedSubFunctor)
         `((WellTypedValue__Stuck <= WTV)%IndexedSubFunctor)

         `{Eval__E : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{WF__Eval__E : ! forall {R}, WellFormedProgramAlgebra Eval__If2 Eval__E (T := R)}
         (recEval : WellFormedValue E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__If2 TypeOf__E (T := R)}
         (recTypeOf : WellFormedValue E -> TypeOfResult T)

        `{PA__TypeEqualityCorrectness :
            ! ProofAlgebra ForTypeEqualityCorrectness T
              (sig (UniversalPropertyP typeEqualityCorrectnessStatement))}
        `{! WellFormedProofAlgebra PA__TypeEqualityCorrectness}

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
      repeat rewrite unwrapUP'_wrapF /=.
      repeat rewrite fmapFusion /=.
      rewrite / Extras.compose /=.
      repeat rewrite wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      repeat rewrite wellFormedProgramAlgebra.
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
  Qed.

End If2.
