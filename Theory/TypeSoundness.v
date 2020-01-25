From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Environment.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Record TypedExpr (* cf. WFValue_i *)
       T E `{FunctorLaws T} `{FunctorLaws E}
  : Set
  := MkTypedValue (* cf. mk_WFValue_i *)
       {
         type : UniversalPropertyF T;
         expr : UniversalPropertyF E;
       }.
Arguments MkTypedValue {T E _ _ _ _}.

(**
In MTC, this is parameterized by some indexed relation.  In practice I don't
think I am using it yet, so leaving it hardcoded until it becomes necessary.
*)

Definition WellTyped
           {T E}
           `{FunctorLaws T} `{FunctorLaws E}
           (WT : (TypedExpr T E)-indexedProp)
           t e
  : Prop
  := IndexedFix WT {| type := t; expr := e; |}.

(**
This is the most abstract statement of the type soundness of evaluation.

Instead of explicitly calling recursively [evalL] and [typeOfL], this is
abstracted over the operation to run recursively, namely [recEval] and
[recTypeOf].

 *)

Definition SoundnessStatement__EvalAlgebra (* cf. eval_alg_Soundness_P *)
           {T E F V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws F} `{FunctorLaws V}
           (WT : (TypedExpr T V -> Prop) -> TypedExpr T V -> Prop)
           `{eval__E   : forall {R}, MixinAlgebra E R (EvalResult   V)}
           `{typeOf__F : forall {R}, MixinAlgebra F R (TypeOfResult T)}
           (recEval   : UniversalPropertyF E -> EvalResult   V)
           (recTypeOf : UniversalPropertyF F -> TypeOfResult T)
           (e : Fix E * Fix F)
           (RFUP_e : Fold__UP' (fst e) /\ Fold__UP' (snd e))
  : Prop
  :=
    forall

      (* Commenting those out temporarily to see where they are needed! *)

      (* recEvalProj : forall (e : UniversalPropertyF L),
          recEval e
          =
          recEval (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig e)))
      *)

      (* recTypeOfProj : forall (e : UniversalPropertyF L'),
          recTypeOf e
          =
          recTypeOf (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig e)))
      *)

      Gamma

      (IH : forall (Gamma : Environment (ValueFix V))
              (a : UniversalPropertyF E * UniversalPropertyF F),
          (forall (tau : TypeFix T),
              typeOf__F recTypeOf (unwrap__UP' (proj1_sig (snd a))) = Some tau ->
              WellTyped WT tau (eval__E recEval (unwrap__UP' (proj1_sig (fst a))) Gamma)
          ) ->
          forall (tau : TypeFix T),
            recTypeOf (snd a) = Some tau ->
            WellTyped WT tau (recEval (wrap__UP' (unwrap__UP' (proj1_sig (fst a)))) Gamma)
      )
    ,
    forall (tau : TypeFix T),
      typeOf__F recTypeOf (unwrap__UP' (snd e)) = Some tau ->
      WellTyped WT tau (eval__E recEval (unwrap__UP' (fst e)) Gamma).

Definition Soundness__EvalAlgebra
           {T E V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
           (WT : (TypedExpr T V -> Prop) -> TypedExpr T V -> Prop)
           `{Eval__E   : forall {R}, ProgramAlgebra Eval   E R (EvalResult   V)}
           `{TypeOf__E : forall {R}, ProgramAlgebra TypeOf E R (TypeOfResult T)}
  := forall recEval recTypeOf,
    ProofAlgebra
      E
      (sig
         (UniversalPropertyP2
            (SoundnessStatement__EvalAlgebra
               (eval__E   := fun _ => programAlgebra' Eval__E)
               (typeOf__F := fun _ => programAlgebra' TypeOf__E)
               WT
               recEval recTypeOf
      ))).

Definition SoundnessStatement__Eval
           {T E V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
           (WT : (TypedExpr T V -> Prop) -> TypedExpr T V -> Prop)
           `{Eval__E   : forall {R}, ProgramAlgebra Eval   E R (EvalResult   V)}
           `{TypeOf__E : forall {R}, ProgramAlgebra TypeOf E R (TypeOfResult T)}
           (recEval   : UniversalPropertyF E -> EvalResult   V)
           (recTypeOf : UniversalPropertyF E -> TypeOfResult T)
           (e : Fix E)
           (RFUP_e : Fold__UP' e)
  : Prop
  :=
    forall Gamma (tau : TypeFix T),
      typeOf e = Some tau ->
      WellTyped WT tau (eval e Gamma).

Lemma Soundness__Eval
      {T E V}
      `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
      (WT : (TypedExpr T V -> Prop) -> TypedExpr T V -> Prop)
      `{Eval__E   : forall {R}, ProgramAlgebra Eval   E R (EvalResult   V)}
      `{TypeOf__E : forall {R}, ProgramAlgebra TypeOf E R (TypeOfResult T)}
      `{WFEval__E : ! WellFormedMendlerAlgebra (@Eval__E)}
      (soundness__EvalAlgebra : Soundness__EvalAlgebra WT)
      (WF_eval_Soundness_alg_F :
         forall recEval recTypeOf,
           WellFormedProofAlgebra2 (soundness__EvalAlgebra recEval recTypeOf)
      )
  : forall (e : WellFormedValue E) Gamma (tau : TypeFix T),
    typeOf (proj1_sig e) = Some tau ->
    WellTyped WT tau (eval (proj1_sig e) Gamma).
Proof.
  move => e Gamma tau TO.
  rewrite <- (wrap_unwrap__UP' _ (proj1_sig e)).
  {
    rewrite // / eval / mendlerFold / wrap__UP' / wrap__F /=.
    rewrite wellFormedMendlerAlgebra.
    rewrite / mendlerFold.
    elim (
        Induction2
          (PA := soundness__EvalAlgebra (fun e => eval (proj1_sig e)) (fun e => typeOf (proj1_sig e)))
          _
          (proj2_sig e)
      ).
    rewrite / SoundnessStatement__EvalAlgebra.
    move => e' E'.
    eapply E'.
    move => Gamma' [[f F][g G]].
    rewrite wrap_unwrap__UP' /=.
    rewrite / eval / mendlerFold / unwrap__F / programAlgebra'.
    admit.
Admitted.
