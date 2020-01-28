From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Semantics.Static Require Import If2.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section If2.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports Stuck}
  .

  Definition eval__If2
    : forall {T}, MixinAlgebra If2 T (EvalResult V)
    := fun _ rec '(MkIf2 condition thenBranch elseBranch) env =>
         match project__F (rec condition env) with
         | Some (MkBool b) =>
           if b
           then rec thenBranch env
           else rec elseBranch env
         | None => stuck "The condition of a binary branch was not a boolean"
         end.

  Global Instance Eval__If2
    : forall {T}, ProgramAlgebra ForEval If2 T (EvalResult V)
    := fun _ => {| programAlgebra := eval__If2; |}.

  Definition Eval__If2'
    : forall T, ProgramAlgebra ForEval If2 T (EvalResult V)
    := fun _ => Eval__If2.

  Global Instance WellFormedMendlerAlgebra_Eval__If2
    : WellFormedMendlerAlgebra Eval__If2'.
  Proof.
    constructor.
    move => T T' f rec [] //.
  Qed.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}

    {E}
    `{FunctorLaws E}
    `{! E supports If2}
    `{! WellFormedSubFunctor If2 E}

    `{! V supports If2}

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
         (recEval   : UniversalPropertyF E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__If2 TypeOf__E (T := R)}
         (recTypeOf : UniversalPropertyF E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness If2
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WT recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2Algebra__If2.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    move => c t e H__c H__t H__e.
    (* )[[UP'__c1 UP'__c2] IH__c] [[UP'__t1 UP'__t2] IH__t] [[UP'__e1 UP'__e2] IH__e] /=. *)
    constructor.
    {
      apply conj; apply (proj2_sig (if2 _ _ _)).
    }
    {
      move => Gamma.
      rewrite / if2__F / if2 / inject /=.
      repeat rewrite unwrap__UP'_wrap__F /=.
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
      (* rewrite / project__F /=. *)
      (* econstructor => //. *)
      (* move : c H__c TY => [a b] H__ab TY /=. *)
      (* move : TY => /=. *)
      (* move => [] <- //. *)


  Admitted.

  Inductive EvalRelation__If2
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | If2True : forall c t e t',
        EvalRelation__E (c, boolean true) ->
        EvalRelation__E (t, t') ->
        EvalRelation__If2 EvalRelation__E (if2 c t e, t')
    | If2False : forall c t e e',
        EvalRelation__E (c, boolean false) ->
        EvalRelation__E (e, e') ->
        EvalRelation__If2 EvalRelation__E (if2 c t e, e')
  .

End If2.
