From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler Require Import

     Semantics.Dynamic.Eval.Unit
     Semantics.Static.TypeOf
     Semantics.Static.TypeOf.Unit
     Semantics.Static.WellTyped.Unit

     Syntax.Terms.Unit
     Syntax.Types.UnitType

     Theory.Algebra
     Theory.Eval
     Theory.SubFunctor
     Theory.Functor
     Theory.IndexedAlgebra
     Theory.IndexedFunctor
     Theory.IndexedSubFunctor
     Theory.ProofAlgebra
     Theory.ProgramAlgebra
     Theory.Types
     Theory.TypeSoundness
     Theory.UniversalProperty

.

Local Open Scope SubFunctor.

(* Section AbstractLemma. *)

(*   Context *)
(*     {T} *)
(*     `{Functor T} *)
(*     {C} *)
(*     `{Functor C} *)
(*     {E} *)
(*     `{Functor E} *)
(*     `{! E supports C} *)
(*     `{! WellFormedSubFunctor C E} *)
(*     {V} *)
(*     `{Functor V} *)
(*   . *)

(*   Theorem EvenMoreAbstractSoundness *)
(*          (WT__C : (TypedExpr T V)-indexedPropFunctor) *)
(*          (WT__E : (TypedExpr T V)-indexedPropFunctor) *)
(*          `(IndexedFunctor (TypedExpr T V) WT__C) *)
(*          `(IndexedFunctor (TypedExpr T V) WT__E) *)
(*          `(! IndexedSubFunctor WT__C WT__E) *)

(*          `{Eval__C   : forall {R}, ProgramAlgebra ForEval   C R (EvalResult   V)} *)
(*          `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)} *)
(*          `{! forall {R}, WellFormedProgramAlgebra Eval__C Eval__E (T := R)} *)
(*          (recEval   : WellFormedValue E -> EvalResult   V) *)

(*          `{TypeOf__C : forall {R}, ProgramAlgebra ForTypeOf C R (TypeOfResult T)} *)
(*          `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)} *)
(*          `{! forall {R}, WellFormedProgramAlgebra TypeOf__C TypeOf__E (T := R)} *)
(*          (recTypeOf : WellFormedValue E -> TypeOfResult T) *)

(*          Gamma (ctor : C (WellFormedValue E)) *)

(*     : *)
(*       (forall *)
(*           (Gamma' : Environment.Environment (ValueFix V)) *)
(*           (a : WellFormedValue E * WellFormedValue E), *)
(*           (forall tau : TypeFix T, *)
(*               programAlgebra' TypeOf__E recTypeOf (unwrapUP' (proj1_sig (snd a))) = *)
(*               Some tau -> *)
(*               WellTyped WT__E tau *)
(*                         (programAlgebra' Eval__E recEval (unwrapUP' (proj1_sig (fst a))) *)
(*                                          Gamma')) -> *)
(*           forall tau : TypeFix T, *)
(*             recTypeOf (snd a) = Some tau -> *)
(*             WellTyped WT__E tau (recEval (wrapUP' (unwrapUP' (proj1_sig (fst a)))) Gamma')) -> *)
(*       forall tau : TypeFix T, *)
(*         programAlgebra' TypeOf__E recTypeOf (unwrapUP' (proj1_sig (inject ctor))) = Some tau -> *)

(*         (WT__C (IndexedFix WT__E) ({| *)
(*              type := tau; *)
(*              expr := programAlgebra' Eval__E recEval (unwrapUP' (proj1_sig (inject ctor))) Gamma; *)
(*            |})) -> *)


(*         WellTyped WT__E tau *)
(*                   (programAlgebra' Eval__E recEval (unwrapUP' (proj1_sig (inject ctor))) Gamma). *)
(*   Proof. *)
(*     rewrite / inject /=. *)
(*     rewrite unwrapUP'_wrapF /=. *)
(*     rewrite fmapFusion / Extras.compose /=. *)
(*     rewrite wellFormedSubFunctor => //=. *)
(*     rewrite / programAlgebra'. *)
(*     rewrite wellFormedProgramAlgebra. *)
(*     rewrite wellFormedProgramAlgebra. *)
(*     move => IH tau TY. *)
(*     apply (iInject (F := WT__C)) => /=. *)
(*   Qed. *)

(* End AbstractLemma. *)

Section Unit.

  Context
    {V}
    `{Functor V}
    `{! V supports Unit}

    {E}
    `{Functor E}
    `{! E supports Unit}

    {T}
    `{Functor T}
    `{! T supports UnitType}
  .

  Global Instance Soundness__Unit

         (WT : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WT)
         `((WellTyped__Unit <= WT)%IndexedSubFunctor)

         `{Eval__E : ! forall R, ProgramAlgebra ForEval E R (EvalResult V)}
         `{! forall R, WellFormedCompoundProgramAlgebra (Eval__E R) (Eval__Unit R)}
         (recEval : WellFormedValue E -> EvalResult V)

         `{TypeOf__E : ! forall R, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall R, WellFormedCompoundProgramAlgebra (TypeOf__E R) (TypeOf__Unit R)}
         (recTypeOf : WellFormedValue E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness Unit
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WT recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2Algebra__Unit.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    constructor.
    {
      apply conj; apply (proj2_sig unit).
    }
    {
      move => Gamma.
      rewrite / unitF / unit / inject /=.
      rewrite unwrapUP'_wrapF /=.
      rewrite fmapFusion / Extras.compose /=.
      rewrite wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      rewrite !wellFormedCompoundProgramAlgebra.
      move => IH tau TY.
      apply (iInject (F := WellTyped__Unit)) => /=.
      econstructor => //.
      move : TY => /=.
      move => [] <- //.
    }
  Qed.

End Unit.
