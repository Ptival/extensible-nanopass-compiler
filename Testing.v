From Coq Require Import String.

From ExtensibleCompiler Require Import Algebra.
From ExtensibleCompiler Require Import Eval.
From ExtensibleCompiler Require Import Functor.
From ExtensibleCompiler Require Import SubFunctor.
From ExtensibleCompiler Require Import Sum1.
From ExtensibleCompiler Require Import UniversalProperty.

From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import If1.
From ExtensibleCompiler.Features Require Import If2.
From ExtensibleCompiler.Features Require Import Stuck.
From ExtensibleCompiler.Features Require Import Unit.

Local Open Scope Sum1_scope.
Local Open Scope SubFunctor_scope.

(* NOTE: This is currently broken *)
Definition e1
  : WellFormedValue (BoolF + If1F + UnitF)
  := if1 (boolean true) unit.

Definition check1 := evalAlgebra (F := UnitF) (R := UnitF).
Definition check2 := evalAlgebra (F := BoolF) (R := UnitF + BoolF).
Definition check3 := evalAlgebra (F := BoolF) (R := BoolF + UnitF).
Definition check4 := evalAlgebra (F := UnitF + BoolF) (R := BoolF + UnitF).

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

Definition checkEvalAssoc := evalAlgebra (F := UnitF + (If1F + BoolF))
                                         (R := (UnitF + If1F) + BoolF).

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

Notation "'Lang0'" := (UnitF + (If1F + BoolF)) (only parsing).
Notation "'Lang1'" := (UnitF + (BoolF + If1F)) (only parsing).

(* Global *)
(*   Instance *)
(*   EvalParallelDispatch *)
(*   {F G L R} `{Eval F L} `{Eval G R} *)
(*   : Eval (F + G) (L + R) *)
(*   | 7. *)
(* Admitted. *)

(* Definition checkEvalSymAssoc := evalAlgebra (F := UnitF + (If1F + BoolF)) *)
(*                                             (R := UnitF + (BoolF + If1F)). *)

(* Definition foo : Eval (UnitF + (If1F + BoolF)) *)
(*                       ((UnitF + If1F) + BoolF). *)
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

Definition bar : Eval ((UnitF + If1F) + BoolF)
                      (BoolF + (UnitF + If1F)).
  apply EvalSym.
Defined.

(* Definition checkEvalSymAssoc2 := evalAlgebra (F := UnitF + (If1F + BoolF)) *)
(*                                             (R := BoolF + (If1F + UnitF)). *)

(* Definition checkEvalSymAssoc3 := evalAlgebra (F := UnitF + (If1F + BoolF)) *)
(*                                             (R := BoolF + (UnitF + If1F)). *)

(* Definition checkEvalSymAssoc4 := evalAlgebra (F := UnitF + (If1F + BoolF)) *)
(*                                              (R := (BoolF + UnitF) + If1F). *)

(* Definition checkEvalForE1_1 := evalAlgebra (F := If1F) *)
(*                                            (R := BoolF + UnitF + If2F). *)

Definition e2 : Fix (BoolF + If2F + StuckF + UnitF)
  := mendlerFold evalAlgebra e1.

Definition checkEvalSym := evalAlgebra (F := UnitF + BoolF)
                                       (R := BoolF + UnitF).

Definition e1WithoutIf1 : Fix (BoolF + If2F + StuckF + UnitF) := mendlerFold evalAlgebra e1.

Inductive Expr : Set :=
| EBool (boolean : bool)
| EIf2 (condition : Expr) (thenBranch : Expr) (elseBranch : Expr)
| EUnit
| EStuck (reason : string)
.

Definition exprBool  {A}     '(Bool b : BoolF A)     := EBool b.
Definition exprIf2   {A} rec '(If2 c t e : If2F A)   := EIf2 (rec c) (rec t) (rec e).
Definition exprUnit  {A}     '(Unit      : UnitF A)  := EUnit.
Definition exprStuck {A}     '(Stuck r   : StuckF A) := EStuck r.

Definition result1 :=
  e1WithoutIf1
    Expr
    (fun A rec => exprBool || exprIf2 rec || exprStuck || exprUnit).

Compute result1.

Definition withoutIf2 : Fix (BoolF + StuckF + UnitF) :=
  mendlerFold evalAlgebra e1WithoutIf1.

Definition withoutIf2' : Fix (BoolF + StuckF + UnitF) := mendlerFold evalAlgebra e1WithoutIf1.

(* Definition e1 : Fix (UnitF + If1F) := if1 unit unit. *)

Definition result2 :=
  withoutIf2'
    Expr
    (fun A rec => exprBool || exprStuck || exprUnit).

Compute result2.

(* Class WellFormedEval {F G} `{Eval F} `{Eval G} `{SubFunctor F G} := *)
(*   { *)
(*     wellFormedEvalAlgebra : forall R rec (e : F R), evalAlgebra rec (inj e : G R) = evalAlgebra rec e; *)
(*   }. *)

(* Definition ValueF := BoolF + StuckF + UnitF. *)

(* Definition ProgramF := ValueF + If1F + If2F. *)

Inductive EvalIf2F_1
          (E V : Set -> Set)
          `{Functor E} `{Functor V}
          `{E supports If2F}
          `{V supports BoolF}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop :=
| MkEvalIF2F_1 e v condition thenBranch elseBranch
  :
    proj1_sig e = if2 condition thenBranch elseBranch ->
    _ ->
    proj1_sig v = boolean true ->
    EvalIf2F_1 E V (e, v)
.
