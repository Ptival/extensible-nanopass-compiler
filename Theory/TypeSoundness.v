From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Environment
     Eval
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedProofAlgebra
     IndexedSubFunctor
     ProofAlgebra
     ProgramAlgebra
     SubFunctor
     Types
     UniversalProperty
.

From ExtensibleCompiler.Semantics.Static Require Import
     TypeOf
.

Local Open Scope SubFunctor.

Record TypedExpr (* cf. WFValue_i *)
       T E
       `{Functor T} `{Functor E}
  : Set
  := MkTypedExpr (* cf. mk_WFValue_i *)
       {
         type : WellFormedValue T;
         expr : WellFormedValue E;
       }.
Arguments type {T E _ _} _.
Arguments expr {T E _ _} _.

(**
We will try and use [TypedValue] when we mean for the expression to only be a
value, though the type system does not guarantee it and this is just an alias.
 *)
Definition TypedValue := TypedExpr.
Arguments TypedValue T E {_ _}.

(**
In MTC, this is parameterized by some indexed relation.  In practice I don't
think I am using it yet, so leaving it hardcoded until it becomes necessary.
 *)

Definition WellTyped {T E}
           `{Functor T} `{Functor E}
           (WT : (TypedExpr T E)-indexedPropFunctor)
           t e
  : Prop
  := IndexedFix WT {| type := t; expr := e |}.

(**
This is the most abstract statement of the type soundness of evaluation.

Instead of explicitly calling recursively [evalL] and [typeOfL], this is
abstracted over the operation to run recursively, namely [recEval] and
[recTypeOf].
 *)

Definition AbstractSoundnessStatement (* cf. eval_alg_Soundness_P *)
           {T E F V}
           `{Functor T} `{Functor E} `{Functor F} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           (*WellFormedEnvironment : Environment (ValueFix V) -> Prop*)
           `{eval__E   : forall {R}, MixinAlgebra E R (EvalResult   V)}
           `{typeOf__F : forall {R}, MixinAlgebra F R (TypeOfResult T)}
           (recEval   : WellFormedValue E -> EvalResult   V)
           (recTypeOf : WellFormedValue F -> TypeOfResult T)
           (e : Fix E * Fix F)
           (RFUP_e : FoldUP' (fst e) /\ FoldUP' (snd e))
  : Prop
  :=
    forall

      (* Commenting those out temporarily to see where they are needed! *)

      (* recEvalProj : forall (e : WellFormedValue L), *)
      (*           recEval e *)
      (*           = *)
      (*           recEval (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig e))) *)
      (*       *)

      (* recTypeOfProj : forall (e : WellFormedValue L'), *)
      (*           recTypeOf e *)
      (*           = *)
      (*           recTypeOf (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig e))) *)
      (*       *)

      Gamma

      (IH : forall (Gamma : Environment (ValueFix V))
              (*WF__Gamma : WellFormedEnvironment Gamma*)
              (a : WellFormedValue E * WellFormedValue F),
          (forall (tau : TypeFix T),
              typeOf__F recTypeOf (unwrapUP' (proj1_sig (snd a))) = Some tau ->
              WellTyped WT tau (eval__E recEval (unwrapUP' (proj1_sig (fst a))) Gamma)
          ) ->
          forall (tau : TypeFix T),
            recTypeOf (snd a) = Some tau ->
            WellTyped WT tau (recEval (wrapUP' (unwrapUP' (proj1_sig (fst a)))) Gamma)
      )
    ,
    forall (tau : TypeFix T),
      typeOf__F recTypeOf (unwrapUP' (snd e)) = Some tau ->
      WellTyped WT tau (eval__E recEval (unwrapUP' (fst e)) Gamma).

Variant ForSoundness := .

Definition Soundness__ProofAlgebra
           {T E V}
           `{Functor T} `{Functor E} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : forall R, ProgramAlgebra ForEval   E R (EvalResult   V)}
           `{TypeOf__E : forall R, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
  := forall recEval recTypeOf,
    ProofAlgebra ForSoundness
                 E
                 (sig
                    (UniversalPropertyP2
                       (AbstractSoundnessStatement
                          (eval__E   := fun _ => programAlgebra)
                          (typeOf__F := fun _ => programAlgebra)
                          WT
                          recEval recTypeOf
                 ))).

Lemma Soundness
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      (WT : (TypedExpr T V)-indexedPropFunctor)
      `{Eval__E : forall R, ProgramAlgebra ForEval E R (EvalResult V)}
      `{! WellFormedMendlerProgramAlgebra Eval__E}
      `{TypeOf__E : forall R, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
      `{! WellFormedMendlerProgramAlgebra TypeOf__E}
      (soundness__ProofAlgebra : Soundness__ProofAlgebra WT)
      (WF_eval_Soundness_alg_F :
         forall recEval recTypeOf,
           WellFormedProofAlgebra2 (soundness__ProofAlgebra recEval recTypeOf)
      )
  : forall (e : WellFormedValue E) Gamma (tau : TypeFix T),
    typeOf (proj1_sig e) = Some tau ->
    WellTyped WT tau (eval (proj1_sig e) Gamma).
Proof.
  move => e Gamma tau TO.
  rewrite <- (wrapUP'_unwrapUP' (proj1_sig e) (proj2_sig e)).
  rewrite /= / eval / mendlerFold / wrapF.
  rewrite wellFormedMendlerProgramAlgebra / mendlerFold.

  pose proof (
      Induction2
        (PA := soundness__ProofAlgebra (fun e => eval (proj1_sig e)) (fun e => typeOf (proj1_sig e)))
        _
        (proj2_sig e)
    ).

  elim (
      Induction2
        (PA := soundness__ProofAlgebra (fun e => eval (proj1_sig e)) (fun e => typeOf (proj1_sig e)))
        _
        (proj2_sig e)
    ) => e' E'.
  apply : E'.
  (* Missing: one premise *)
  (* Missing: one premise *)
  {
    move => Gamma' a IH tau1 TY1.
    rewrite / eval / mendlerFold /= / wrapF.
    rewrite wellFormedMendlerProgramAlgebra.
    rewrite / mendlerFold.
    apply : IH.
    {
      rewrite <- (wrapUP'_unwrapUP' (proj1_sig (snd a)) (proj2_sig (snd a))) in TY1.
      rewrite /= in TY1.
      rewrite / typeOf / mendlerFold / wrapF in TY1.
      erewrite wellFormedMendlerProgramAlgebra in TY1 => //.
    }
  }
  {
    rewrite <- (wrapF_unwrapF (proj1_sig e) (proj2_sig e)) in TO.
    rewrite / typeOf / mendlerFold / wrapF /= in TO.
    rewrite / programAlgebra'.
    erewrite <- wellFormedMendlerProgramAlgebra => //.
    rewrite /= / unwrapUP'.
    erewrite Fusion.
    {
      eapply TO.
    }
    {
      move => a.
      do 2 rewrite fmapFusion => //.
    }
  }
Qed.

(**
A more concise version of [AbstractSoundnessStatement], to be used in client
files.
 *)
Definition AbstractSoundnessStatement'
           {T E V}
           `{Functor T} `{Functor E} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : forall R, ProgramAlgebra ForEval   E R (EvalResult   V)}
           `{TypeOf__E : forall R, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
           (recEval   : WellFormedValue E -> EvalResult   V)
           (recTypeOf : WellFormedValue E -> TypeOfResult T)
  :=
    (AbstractSoundnessStatement
       WT
       (eval__E   := fun _ => programAlgebra)
       (typeOf__F := fun _ => programAlgebra)
       recEval recTypeOf
    ).

(**
A nicer version of [AbstractSoundnessStatement], to be used in client files.
 *)
Definition SoundnessStatement
           {T E V}
           `{Functor T} `{Functor E} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : forall R, ProgramAlgebra ForEval   E R (EvalResult   V)}
           `{TypeOf__E : forall R, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
           (recEval   : WellFormedValue E -> EvalResult   V)
           (recTypeOf : WellFormedValue E -> TypeOfResult T)
           (e : Fix E)
           (RFUP_e : FoldUP' e)
  : Prop
  :=
    forall Gamma (tau : TypeFix T),
      typeOf e = Some tau ->
      WellTyped WT tau (eval e Gamma).

(**
The [WellTyped] predicates are indexed by a [TypedExpr], which is a pair of a
[WellFormed] type and a [WellFormed] expression.  Recall that [WellFormed] is a
dependent pair of an extensible term, and a proof that it satisfies the
universal property of folds.

Unfortunately, we do not have an automatic means of proof irrelevance with
respect to that proof.  This means that if we have a [TypedExpr] like:

[{| type := exist tau1 UP'__tau1; expr := exist e1 UP'__e1 |}]

and we are trying to prove:

[{| type := exist tau2 UP'__tau2; expr := exist e2 UP'__e2 |}]

it does not suffice to show that [tau1 = tau2] and [e1 = e2], as the [TypedExpr]
are not convertible unless [UP'__tau1 = UP'__tau2] and [UP'__e1 = UP'__e2] .

[WellTypedProj1Type] is an extensible property of [WellTyped] properties,
capturing those that are well-formed in the sense that they are preserved as
long as the first projection of their type is preserved.

[WellTypedProj1Expr] is an extensible property of [WellTyped] properties,
capturing those that are well-formed in the sense that they are preserved as
long as the first projection of their expression is preserved.

All [WellTyped] properties will satisfy both of these properties, so that we can
combine them to move [WellTyped]-ness across equal types or expressions.
 *)

Definition PropertyStatement__WellTypedProj1Type
           {T V}
           `{Functor T} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           (te : TypedExpr T V)
  := forall tau' UP',
    tau' = proj1_sig (type te) ->
    WellTyped WT (exist _ tau' UP') (expr te).

Variant ForWellTypedProj1Type := .

Definition wellTypedProj1Type
           {T V}
           `{Functor T} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{! IndexedFunctor (TypedExpr T V) WT}
           `{A : ! IndexedProofAlgebra
                   ForWellTypedProj1Type
                   WT
                   (PropertyStatement__WellTypedProj1Type WT)
            }
  := ifold (indexedProofAlgebra' A).

Definition PropertyStatement__WellTypedProj1Expr
           {T V}
           `{Functor T} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           (te : TypedExpr T V)
  := forall e' UP',
    e' = proj1_sig (expr te) ->
    WellTyped WT (type te) (exist _ e' UP').

Variant ForWellTypedProj1Expr := .

Definition wellTypedProj1Expr
           {T V}
           `{Functor T} `{Functor V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{! IndexedFunctor (TypedExpr T V) WT}
           `{A : ! IndexedProofAlgebra
                   ForWellTypedProj1Expr
                   WT
                   (PropertyStatement__WellTypedProj1Expr WT)
            }
  := ifold (indexedProofAlgebra' A).
