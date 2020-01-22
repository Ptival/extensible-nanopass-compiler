From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Theory Require Import Algebra.
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

Definition eval_Bool
           {O} `{FunctorLaws O} `{! SubFunctor Bool O}
           (R : Set) (rec : R -> Fix O)
           (e : Bool R)
  : Fix O
  := match e with MkBool b => boolean b end.

Global Instance Eval_Bool__WF
       {O} `{FunctorLaws O}
       `{! SubFunctor Bool O}
       T
  : ProgramAlgebra Bool T (WellFormedValue O)
  | 0 :=
  {| programAlgebra := fun rec '(MkBool b) => boolean' b; |}.

Definition eval_Bool_1 (e : Fix Bool) : WellFormedValue Bool
  := mendlerFold (fun _ => programAlgebra) e.

Global Instance Eval_Bool__Fix
       {O} `{FunctorLaws O}
       `{! SubFunctor Bool O}
       T
  : ProgramAlgebra Bool T (Fix O)
  | 0 :=
  {| programAlgebra := eval_Bool T; |}.

Inductive Eval_Bool {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! SubFunctor Bool E} `{! SubFunctor Bool V}
          (Eval_E : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | BoolValue : forall b, Eval_Bool Eval_E (boolean' b, boolean' b)
.

Record WFValue_i
       V LT
       `{FunctorLaws V}
       `{FunctorLaws LT}
  : Set :=
    mk_WFValue_i { wfv_a : UniversalPropertyF V; wfv_b : UniversalPropertyF LT; }.

(**
In MTC, this is parameterized by some indexed relation.  In practice I don't
think I am using it yet, so leaving it hardcoded until it becomes necessary.
*)

Definition WFValue
           V LT
           `{FunctorLaws V} `{FunctorLaws LT}
           (* WFV : (WFValue_i V LT -> Prop) -> WFValue_i V LT -> Prop *)
  : WFValue_i V LT -> Prop
  := IndexedFix (fun _ _ => True) (* should be WFV *).

Definition WFValueC
           {V LT}
           `{FunctorLaws V} `{FunctorLaws LT}
           (*WFV : (WFValue_i V LT)-relation*)
           v lt
  := WFValue V LT (*WFV*) (mk_WFValue_i V LT _ _ _ _ v lt).

(**
This is the most abstract statement of the type soundness of evaluation.

Instead of explicitly calling recursively [evalL] and [typeOfL], this is
abstracted over the operation to run recursively, namely [recEval] and
[recTypeOf].

 *)

Definition eval_alg_Soundness_P
           {L L' LT V}
           `{FunctorLaws L} `{FunctorLaws L'} `{FunctorLaws LT} `{FunctorLaws V}
           (*WFV : (WFValue_i V LT -> Prop) -> WFValue_i V LT -> Prop*)
           `{evalL   : forall {T}, MixinAlgebra T L (EvalResult V)}
           `{typeOfL : forall {T}, MixinAlgebra T L' (TypeOfResult LT)}
           (recEval : UniversalPropertyF L -> EvalResult V)
           (recTypeOf : UniversalPropertyF L' -> TypeOfResult LT)
           (e : Fix L' * Fix L)
           (RFUP_e : ReverseFoldUniversalProperty (fst e) /\ ReverseFoldUniversalProperty (snd e))
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

      (IH : forall (a : UniversalPropertyF L' * UniversalPropertyF L),
          (forall T,
              typeOfL recTypeOf (reverseFoldUnwrapFix (proj1_sig (fst a))) = Some T ->
              WFValueC (*WFV*) (evalL recEval (reverseFoldUnwrapFix (proj1_sig (snd a)))) T
          ) ->
          forall T,
            recTypeOf (fst a) = Some T ->
            WFValueC (*WFV*) (recEval (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig (snd a))))) T
      )
    ,
    forall (T : TypeFix LT),
      typeOfL recTypeOf (reverseFoldUnwrapFix (fst e)) = Some T ->
      WFValueC (*WFV*) (evalL recEval (reverseFoldUnwrapFix (snd e))) T.

Definition Eval_Soundness_alg_F
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           (WFV : (WFValue_i V LT -> Prop) -> WFValue_i V LT -> Prop)
           `{EvalL   : forall {T}, ProgramAlgebra L T (EvalResult V)}
           `{TypeOfL : forall {T}, ProgramAlgebra L T (TypeOfResult LT)}
  := forall recTypeOf recEval,
    ProofAlgebra
      L
      (sig
         (UniversalPropertyP2
            (eval_alg_Soundness_P
               (evalL   := fun _ => programAlgebra' EvalL)
               (typeOfL := fun _ => programAlgebra' TypeOfL)
               (*fun _ _ => True*)
               recTypeOf recEval
      ))).

Definition eval_Soundness_P
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           (*WFV : (WFValue_i V LT -> Prop) -> WFValue_i V LT -> Prop*)
           `{EvalL   : forall {T}, ProgramAlgebra L T (EvalResult V)}
           `{TypeOfL : forall {T}, ProgramAlgebra L T (TypeOfResult LT)}
           (recEval : UniversalPropertyF L -> EvalResult V)
           (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
           (e : Fix L)
           (RFUP_e : ReverseFoldUniversalProperty e)
  : Prop
  :=
    forall (T : TypeFix LT),
      typeOf e = Some T ->
      WFValueC (*WFV*) (eval e) T.

Lemma eval_Soundness
      {L LT V}
      `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
      (*WFV : (WFValue_i V LT -> Prop) -> WFValue_i V LT -> Prop*)
      `{EvalL   : forall {T}, ProgramAlgebra L T (EvalResult V)}
      `{TypeOfL : forall {T}, ProgramAlgebra L T (TypeOfResult LT)}
      `{WFEvalL : ! WellFormedMendlerAlgebra (@EvalL)}
      (eval_Soundness_alg_F
       : Eval_Soundness_alg_F
           (fun (_ : WFValue_i V LT -> Prop) (_ : WFValue_i V LT) => True) (* should be WFV*)
      )
      (WF_eval_Soundness_alg_F :
         forall recTypeOf recEval,
           WellFormedProofAlgebra2 (eval_Soundness_alg_F recTypeOf recEval)
      )
  : forall (e : WellFormedValue L) (T : TypeFix LT),
    typeOf (proj1_sig e) = Some T ->
    WFValueC (*fun _ _ => True*) (eval (proj1_sig e)) T.
Proof.
  move => e T TO.
  setoid_rewrite <- reverseFoldWrapUnwrapFix_inverse.
  {
    rewrite // / eval / mendlerFold / reverseFoldWrapFix / wrapFix /=.
    setoid_rewrite wellFormedMendlerAlgebra.
    rewrite / mendlerFold.
    elim (
        Induction2
          (PA :=
             eval_Soundness_alg_F
               (fun e => eval (proj1_sig e))
               (fun e => typeOf (proj1_sig e))
          )
          _
          (proj2_sig e)
      ).
    rewrite / eval_alg_Soundness_P.
    move => e' E'.
    eapply E'.
    move => [[f F][g G]].
    rewrite reverseFoldWrapUnwrapFix_inverse /=.
    rewrite / eval / mendlerFold / reverseFoldUnwrapFix / programAlgebra'.
    admit.
Admitted.

Definition blit'
           {L}
           `{FunctorLaws L}
           `{! SubFunctor Bool L}
           (b : bool)
  : UniversalPropertyF L :=
  injectUniversalProperty (MkBool b).

Global Instance Soundness_Eval_Bool
       {L LT V}
       `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
       `{! SubFunctor Bool L}
       `{Eval_L   : forall {T}, ProgramAlgebra L T (EvalResult   V)}
       `{TypeOf_L : forall {T}, ProgramAlgebra L T (TypeOfResult LT)}
       (recEval   : UniversalPropertyF L -> EvalResult   V)
       (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
  : ProofAlgebra Bool
      (sig
         (UniversalPropertyP2
            (eval_alg_Soundness_P (*fun _ _ => True*)
               (evalL   := fun _ => programAlgebra' Eval_L)
               (typeOfL := fun _ => programAlgebra' TypeOf_L)
               recEval recTypeOf
      ))).
Proof.
  constructor.
  pose proof (
         Induction2Algebra_Bool
           (@eval_alg_Soundness_P
              _ _ _ _ _ _ _ _ _ _ _
              _
              (fun _ => programAlgebra' (Eval_L   _))
              (fun _ => programAlgebra' (TypeOf_L _))
              recEval
              recTypeOf
           )
       ).
  apply : H5.
  (* apply : Induction2Algebra_Bool => b. *)
  rewrite / eval_alg_Soundness_P / UniversalPropertyP2.
  constructor => /=.
  {
    apply conj; apply : (proj2_sig (boolean' b)).
  }
  {
    admit.
  }
Admitted.
