From Coq Require Import String.

From ExtensibleCompiler.Passes Require Import RemoveUnaryIfs.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedSum1.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope Sum1_scope.
Local Open Scope SubFunctor_scope.

Definition p
  : MixinAlgebra (WellFormedValue (If2 + Unit)) If1 (WellFormedValue (If2 + Unit))
  := programAlgebra.

Definition q := p id.

Definition e1
  : WellFormedValue (Bool + If1 + Unit)
  := if1 (boolean__WF true) unit__WF.

Definition v1
  : Fix (Bool + If1 + Unit)
  := proj1_sig e1.

(* Definition check1 := evalAlgebra (F := Unit) (R := Unit). *)
(* Definition check2 := evalAlgebra (F := Bool) (R := Unit + Bool). *)
(* Definition check3 := evalAlgebra (F := Bool) (R := Bool + Unit). *)
(* Definition check4 := evalAlgebra (F := Unit + Bool) (R := Bool + Unit). *)

Definition MixinAlgebra' I O := MixinAlgebra O I O.

(* From now on, code writes itself, for instance: *)

(* Global Instance removeUnaryIfsManual : *)
(*   ProgramAlgebra *)
(*     (Bool + If1) *)
(*     (WellFormedValue (Bool + If2 + Unit)) *)
(*     (WellFormedValue (Bool + If2 + Unit)) *)
(*   := _. *)

Definition V := WellFormedValue (Bool + If2 + Unit).

(* Definition removeUnaryIfsMixin *)
(*   : MixinAlgebra' (Bool + If1) V *)
(*   := programAlgebra. *)

Definition removeUnaryIfsFromFix
  : Fix (Bool + If1) -> WellFormedValue (Bool + If2 + Unit)
  := fold (programAlgebra id).

Definition evalWellFormed I O `{Functor I} `{Functor O}
           `{ProgramAlgebra I (WellFormedValue O) (WellFormedValue O)}
  : WellFormedValue I -> WellFormedValue O
  := fun v => fold (programAlgebra id) (proj1_sig v).

Definition removeUnaryIfs
  : WellFormedValue (Bool + If1) -> WellFormedValue (Bool + If2 + Unit)
  := evalWellFormed _ _.

Definition exprIf1
  : WellFormedValue (Bool + If1)
  := if1 (boolean__WF true) (boolean__WF false).

Definition exprIf2
  : WellFormedValue (Bool + If2 + Unit)
  := if2__WF (boolean__WF true) (boolean__WF false) unit__WF.

Theorem removeUnaryIfsExprIf1
  : removeUnaryIfs exprIf1 = exprIf2.
Proof.
  reflexivity.
Qed.

Theorem removeUnaryIfsSyntacticCorrectness :
  forall c t,
    removeUnaryIfs (if1 c t) = if2__WF (removeUnaryIfs c) (removeUnaryIfs t) unit__WF.
Proof.
  reflexivity.
Qed.

Delimit Scope IndexedSum1_scope with IndexedSum1.

Definition SourceExpr := Bool + If1.
Definition TargetExpr := Bool + If2 + Unit.
Definition Value := Bool + Stuck + Unit.

Definition SourceEval
  : (WellFormedValue SourceExpr * WellFormedValue Value) -> Prop
  := IndexedFix
    (
      EvalBool SourceExpr Value
      +
      EvalIf1  SourceExpr Value
      (* + *)
      (* EvalUnit SourceExpr Value *)
    )%IndexedSum1.

Definition TargetEval
  : (WellFormedValue TargetExpr * WellFormedValue Value) -> Prop
  := IndexedFix
    (
      EvalBool TargetExpr Value
      +
      EvalIf2  TargetExpr Value
      +
      EvalUnit TargetExpr Value
    )%IndexedSum1.

Theorem removeUnaryIfsCorrectness
  : forall e v,
    SourceEval (e, v) ->
    TargetEval (removeUnaryIfs e, v).
Proof.
  unfold SourceEval, TargetEval.
  intros e v S.
  apply iWrapFix.
  eapply iUnwrapFix in S.
  destruct S.
  {

  }
  apply iWrapFix.
  split.
Qed.






STOP HERE.

Global
  Instance
  EvalAssocRL {F G H} `{Functor F} `{Functor G} `{Functor H}
  : Eval (F + (G + H)) ((F + G) + H) :=
  {|
    evalAlgebra := fun A rec v =>
                     match fmap rec v with
                     | inl1 f        => wrapFix (inl1 (inl1 f))
                     | inr1 (inl1 g) => wrapFix (inl1 (inr1 g))
                     | inr1 (inr1 h) => wrapFix (inr1 h)
                     end;
  |}.

Global
  Instance
  EvalAssocLR {F G H} `{Functor F} `{Functor G} `{Functor H}
  : Eval ((F + G) + H) (F + (G + H)) :=
  {|
    evalAlgebra := fun A rec v =>
                     match fmap rec v with
                     | inl1 (inl1 f) => wrapFix (inl1 f)
                     | inl1 (inr1 g) => wrapFix (inr1 (inl1 g))
                     | inr1 h        => wrapFix (inr1 (inr1 h))
                     end;
  |}.

Definition checkEvalAssoc := evalAlgebra (F := Unit + (If1 + Bool))
                                         (R := (Unit + If1) + Bool).

Global
  Instance
  EvalSym {F G} `{Functor F} `{Functor G}
  : Eval (F + G) (G + F) :=
  {|
    evalAlgebra := fun A rec v =>
                     match fmap rec v with
                     | inl1 f => wrapFix (inr1 f)
                     | inr1 g => wrapFix (inl1 g)
                     end;
  |}.

(* Global *)
(*   Instance *)
(*   EvalTrans {F G H} `{Functor F} `{Functor G} `{Functor H} *)
(*   `{Eval F G} `{Eval G H} *)
(*   : Eval F H *)
(*   | 10 := *)
(*   {| *)
(*     evalAlgebra := fun A rec v => _; *)
(*   |}. *)
(* Admitted. *)


(* Global Instance EvalDistributes {F G H} `{Eval F G} `{Functor H} *)
(*   : Eval F (G + H) := *)
(*   {| *)
(*     evalAlgebra := fun A rec v => _; *)
(*   |}. *)
(* pose proof (fmap rec v). *)
(* pose proof (evalAlgebra (F := F) (R := G)) as E. *)
(* specialize (E (Fix (G + H))). *)
(* admit. *)

(* Global Instance EvalDistributes {F G H} `{Eval F G} `{Functor H} *)
(*   : Eval F (G + H) := *)
(*   {| *)
(*     evalAlgebra := fun A rec v => *)
(*                      let v1 := fmap rec v in *)
(*                      let v2 := fmap unwrapFix v1 in *)
(*                      let v3 := fmap (fun v => match v with *)
(*                                            | inl1 g => _ *)
(*                                            | inr1 h => _ *)
(*                                            end) v2 in *)
(*                      wrapFix _ *)
(*     ; *)
(*   |}. *)
(* admit. *)

(* pose proof (fmap rec v) as v1. *)
(* pose proof (fmap unwrapFix v1) as v2. *)
(* pose proof (fmap (fun v => match v with inl1 g => evalAlgebra g | inr1 h => evalAlgebra h end) v2) as v3. *)
(* (evalAlgebra (F := F) (R := G)) v'). *)


(* intros B recB. *)
(* pose proof (evalAlgebra (R := G + H)) as E. *)
(* eapply E. *)
(* apply rec. *)
(* eapply evalAlgebra. *)
(* eapply wrapFix. *)

Notation "'Lang0'" := (Unit + (If1 + Bool)) (only parsing).
Notation "'Lang1'" := (Unit + (Bool + If1)) (only parsing).

(* Global *)
(*   Instance *)
(*   EvalParallelDispatch *)
(*   {F G L R} `{Eval F L} `{Eval G R} *)
(*   : Eval (F + G) (L + R) *)
(*   | 7. *)
(* Admitted. *)

(* Definition checkEvalSymAssoc := evalAlgebra (F := Unit + (If1 + Bool)) *)
(*                                             (R := Unit + (Bool + If1)). *)

(* Definition foo : Eval (Unit + (If1 + Bool)) *)
(*                       ((Unit + If1) + Bool). *)
(*   apply EvalAssocRL. *)
(* Defined. *)

Global
  Instance
  EvalSubFunctorDispatch
  {F G} `{Functor F} `{Functor G} `{F <= G}
  : Eval F G
  | 5 :=
  {|
    evalAlgebra := fun A rec v => inject (fmap rec v);
  |}.

Definition bar : Eval ((Unit + If1) + Bool)
                      (Bool + (Unit + If1)).
  apply EvalSym.
Defined.

(* Definition checkEvalSymAssoc2 := evalAlgebra (F := Unit + (If1 + Bool)) *)
(*                                             (R := Bool + (If1 + Unit)). *)

(* Definition checkEvalSymAssoc3 := evalAlgebra (F := Unit + (If1 + Bool)) *)
(*                                             (R := Bool + (Unit + If1)). *)

(* Definition checkEvalSymAssoc4 := evalAlgebra (F := Unit + (If1 + Bool)) *)
(*                                              (R := (Bool + Unit) + If1). *)

(* Definition checkEvalForE1_1 := evalAlgebra (F := If1) *)
(*                                            (R := Bool + Unit + If2). *)

Definition e2
  : WellFormedValue (Bool + If2 + Stuck + Unit)
  := injectUniversalProperty e1.

Definition checkEvalSym := evalAlgebra (F := Unit + Bool)
                                       (R := Bool + Unit).

Definition e1WithoutIf1 : Fix (Bool + If2 + Stuck + Unit) := mendlerFold evalAlgebra e1.

Inductive Expr : Set :=
| EBool (boolean : bool)
| EIf2 (condition : Expr) (thenBranch : Expr) (elseBranch : Expr)
| EUnit
| EStuck (reason : string)
.

Definition exprBool  {A}     '(Bool b : Bool A)     := EBool b.
Definition exprIf2   {A} rec '(If2 c t e : If2 A)   := EIf2 (rec c) (rec t) (rec e).
Definition exprUnit  {A}     '(Unit      : Unit A)  := EUnit.
Definition exprStuck {A}     '(Stuck r   : Stuck A) := EStuck r.

Definition result1 :=
  e1WithoutIf1
    Expr
    (fun A rec => exprBool || exprIf2 rec || exprStuck || exprUnit).

Compute result1.

Definition withoutIf2 : Fix (Bool + Stuck + Unit) :=
  mendlerFold evalAlgebra e1WithoutIf1.

Definition withoutIf2' : Fix (Bool + Stuck + Unit) := mendlerFold evalAlgebra e1WithoutIf1.

(* Definition e1 : Fix (Unit + If1) := if1 unit unit. *)

Definition result2 :=
  withoutIf2'
    Expr
    (fun A rec => exprBool || exprStuck || exprUnit).

Compute result2.

(* Class WellFormedEval {F G} `{Eval F} `{Eval G} `{SubFunctor F G} := *)
(*   { *)
(*     wellFormedEvalAlgebra : forall R rec (e : F R), evalAlgebra rec (inj e : G R) = evalAlgebra rec e; *)
(*   }. *)

(* Definition ValueF := Bool + Stuck + Unit. *)

(* Definition ProgramF := ValueF + If1 + If2. *)

Inductive EvalIf2_1
          (E V : Set -> Set)
          `{Functor E} `{Functor V}
          `{E supports If2}
          `{V supports Bool}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop :=
| MkEvalIF2F_1 e v condition thenBranch elseBranch
  :
    proj1_sig e = if2 condition thenBranch elseBranch ->
    _ ->
    proj1_sig v = boolean true ->
    EvalIf2_1 E V (e, v)
.
