From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Semantics Require Import
     Dynamic.Eval.If2
     Static.TypeOf.If2
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
     IndexedSubFunctor
     ProgramAlgebra
     ProofAlgebra
     SubFunctor
     Types
     TypeSoundness
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section If2.

  Context

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports If2}
    `{! V supports Stuck}

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

        (WT : (TypedExpr T V)-indexedPropFunctor)
        `(IndexedFunctor (TypedExpr T V) WT)
        (* `(IndexedFunctor (TypedExpr T V) WellTyped__If2) *)
        `((WellTyped__If2 <= WT)%IndexedSubFunctor)

        `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
        `{! forall {R}, WellFormedProgramAlgebra Eval__If2 Eval__E (T := R)}

        (Eval__R : Set)
        {F} `{FunctorLaws F} `{F supports If2}
        `{Eval__V : ProgramAlgebra ForEval F (EvalResult V) Eval__R}
        `{! forall {R}, WellFormedProgramAlgebra Eval__If2 Eval__E (T := R)}
        recEval

        (TypeOf__R : Set)
        `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
        `{! forall {R}, WellFormedProgramAlgebra TypeOf__If2 TypeOf__E (T := R)}
        recTypeOf

    : forall Gamma (c t e : TypeOf__R) (c' t' e' : Eval__R),

      (forall tau,
          recTypeOf c = Some tau ->
          WellTyped__If2 (IndexedFix WT) {| type := tau; expr := (recEval c' Gamma) |}
      ) ->

      (forall tau,
          recTypeOf t = Some tau ->
          WellTyped__If2 (IndexedFix WT) {| type := tau; expr := (recEval t' Gamma) |}
      ) ->

      (forall tau,
          recTypeOf e = Some tau ->
          WellTyped__If2 (IndexedFix WT) {| type := tau; expr := (recEval e' Gamma) |}
      ) ->

      forall tau,
        typeOf__If2 (R := TypeOf__R) recTypeOf (MkIf2 c t e) = Some tau ->
        WellTyped__If2
          (IndexedFix WT)
          {|
            type := tau;
            expr := eval__If2 (T := Eval__R) recEval (MkIf2 c' t' e') Gamma;
          |}.
  Proof.
    rewrite /=.
    move => Gamma c t e c' t' e'.
    case : (recTypeOf c) => // tau__c H__c.
    move : H__c (H__c tau__c eq_refl) => _ WT__c.
    case : (isBoolType (proj1_sig tau__c)) => //.
    case : (recTypeOf t) => // tau__t H__t.
    move : H__t (H__t tau__t eq_refl) => _ WT__t.
    case : (recTypeOf e) => // tau__e H__e.
    move : H__e (H__e tau__e eq_refl) => _ WT__e.
    move => tau.
    case TE : (typeEquality (proj1_sig tau__t) tau__e) => //.
    move => [] <-.

    (* TODO: implement typeEqualityCorrectness for all types *)

    (* pose proof (typeEqualityCorrectness tau__t tau__e). *)
    (* eapply typeEqualityCorrectness in TE. *)

  Admitted.

  Global Instance Soundness__If2

         (WT : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WT)
         (* `(IndexedFunctor (TypedExpr T V) WellTyped__If2) *)
         `((WellTyped__If2 <= WT)%IndexedSubFunctor)

         `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{! forall {R}, WellFormedProgramAlgebra Eval__If2 Eval__E (T := R)}
         (recEval   : WellFormedValue E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__If2 TypeOf__E (T := R)}
         (recTypeOf : WellFormedValue E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness If2
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WT recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2__If2.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    move => c t e H__c H__t H__e.
    (* )[[UP'__c1 UP'__c2] IH__c] [[UP'__t1 UP'__t2] IH__t] [[UP'__e1 UP'__e2] IH__e] /=. *)
    constructor.
    {
      apply conj; exact (proj2_sig (if2 _ _ _)).
    }
    {
      move => Gamma.
      rewrite / if2F / if2 / inject /=.
      repeat rewrite unwrapUP'_wrapF /=.
      repeat rewrite fmapFusion /=.
      rewrite / Extras.compose /=.
      repeat rewrite wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      repeat rewrite wellFormedProgramAlgebra.
      move => IH tau TY.
      apply (iInject (F := WellTyped__If2)).

      (* econstructor. *)
      (* move : TY. *)
      (* rewrite {1} / programAlgebra. *)
      (* move : (IH__e Gamma). *)
      (* constructor. *)
      (* rewrite / projectF /=. *)
      (* econstructor => //. *)
      (* move : c H__c TY => [a b] H__ab TY /=. *)
      (* move : TY => /=. *)
      (* move => [] <- //. *)


  Admitted.

End If2.
