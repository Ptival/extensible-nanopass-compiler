From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

Notation "L 'supports' F" := (F <= L) (at level 50) : SubFunctor_scope.

Generalizable All Variables.

Class MendlerEval `(FF : Functor F) `(FR : Functor R) :=
  {
    evalMendlerAlgebra : MendlerAlgebra F (Fix R)
  }.

Global
  Instance
  MendlerEvalSum1
  `(FF : Functor F) `(FG : Functor G) `(FR : Functor R)
  `(MFR : ! MendlerEval FF FR) `(MGR : ! MendlerEval FG FR)
  : ! MendlerEval (F + G) R
  | 2 :=
  {|
    evalMendlerAlgebra :=
      fun A rec v =>
        match v with
        | inl1 fa => evalMendlerAlgebra A rec fa
        | inr1 ga => evalMendlerAlgebra A rec ga
        end;
  |}.

Global
  Instance
  MendlerEvalSum1OutputL
  `(FF : Functor F) `(FG : Functor G)
  : ! MendlerEval F (F + G)
  | 3 :=
  {|
    evalMendlerAlgebra := fun A rec v => wrapFix (inl1 (fmap rec v));
  |}.

Global
  Instance
  MendlerEvalSum1OutputR
  `(FF : Functor F) `(FG : Functor G)
  : ! MendlerEval G (F + G)
  | 4 :=
  {|
    evalMendlerAlgebra := fun A rec v => wrapFix (inr1 (fmap rec v));
  |}.

Global Instance MendlerEvalRefl `(Functor F) : ! MendlerEval F F
  | 1 :=
  {|
    evalMendlerAlgebra := fun A rec v => wrapFix (fmap rec v);
  |}.

(**
[T] stands for the recursive occurence.
[F] stands for the input functor.
[A] stands for the output functor.
 *)
Class MixinEval T F A
      (* `{Functor T} `{Functor F} `{Functor A} *) :=
  {
    evalMixinAlgebra : MixinAlgebra (Fix T) F (Fix A)
  }.

Global
  Instance
  MixinEvalSum1
  `(FF : Functor F) `(FG : Functor G)
  `(MFR : ! MixinEval T F R) `(MGR : ! MixinEval T G R)
  : ! MixinEval T (F + G) R
  | 2 :=
  {|
    evalMixinAlgebra :=
      fun rec v S alg =>
        match v with
        | inl1 l => evalMixinAlgebra rec l S alg
        | inr1 r => evalMixinAlgebra rec r S alg
        end;
  |}.

Global
  Instance
  MixinEvalSum1OutputL
  {T} `(FF : Functor F) `(FG : Functor G)
  : MixinEval T F (F + G)
  | 3 :=
  {|
    evalMixinAlgebra := fun rec v S alg => mendlerFold alg (wrapFix (inl1 (fmap rec v)));
  |}.

Global
  Instance
  MixinEvalSum1OutputR
  {T} `(FF : Functor F) `(FG : Functor G)
  : MixinEval T G (F + G)
  | 3 :=
  {|
    evalMixinAlgebra := fun rec v S alg => mendlerFold alg (wrapFix (inr1 (fmap rec v)));
  |}.

Fixpoint boundedFix
         {A} {F} `{Functor F}
         (n : nat)
         (fM : MixinAlgebra (Fix F) F A)
         (default : A)
         (e : Fix F)
  : A
  :=
  match n with
  | 0   => default
  | S n => fM (boundedFix n fM default) (unwrapFix e)
  end.

Class WellFormedMendlerEval
      `{FF : Functor F} `{FG : Functor G} `{FA : Functor A}
      `(MFA : ! MendlerEval FF FA) `(MGA : ! MendlerEval FG FA)
      `(S : F <= G)
  :=
    {
      wellFormedMendlerEval : forall (R : Set) (rec : R -> Fix A) (e : F R),
        evalMendlerAlgebra R rec (inj e) = evalMendlerAlgebra R rec e;
    }.

Global Instance WellFormedMendlerEvalLeft
       `{FF : Functor F} `{FG : Functor G} `{FA : Functor A}
       `{MFA : ! MendlerEval FF FA}
       `{MGA : ! MendlerEval FG FA}
       `{S : F <= G}
       `(WF : ! WellFormedMendlerEval MFA MGA S)
       `{FH : Functor H}
       `(HA : ! MendlerEval FH FA)
  : ! WellFormedMendlerEval F (G + H) A.
Proof.
  constructor.
  intros R rec e.
  unfold evalMendlerAlgebra.
  unfold MendlerEvalSum1.
  apply wellFormedMendlerEval.
Defined.

Global Instance WellFormedMendlerEvalRight
       `{FF : Functor F} `{FH : Functor H} `{FA : Functor A}
       `{MFA : ! MendlerEval FF FA}
       `{MHA : ! MendlerEval FH FA}
       `{S : F <= H}
       `(WF : ! WellFormedMendlerEval MFA MHA S)
       `{FG : Functor G}
       `(GA : ! MendlerEval FG FA)
  : ! WellFormedMendlerEval F (G + H) A.
Proof.
  constructor.
  intros R rec e.
  unfold evalMendlerAlgebra.
  unfold MendlerEvalSum1.
  apply wellFormedMendlerEval.
Defined.

Class WellFormedMixinEval
      `{FF : Functor F} `{FG : Functor G}
      `(TFA : MixinEval T F A) `(TGA : MixinEval T G A)
      `(S : F <= G)
  :=
    {
      wellFormedMixinEval : forall (rec : Fix T -> Fix A) (e : F (Fix T)),
        evalMixinAlgebra rec (inj e) = evalMixinAlgebra rec e
      ;
    }.

Global Instance WellFormedMixinEvalLeft
       `{FF : Functor F} `{FG : Functor G}
       `{MFA : ! MixinEval T F A}
       `{MGA : ! MixinEval T G A}
       `{S : F <= G}
       `(WF : ! WellFormedMixinEval MFA MGA S)
       `{FH : Functor H}
       `(HA : ! MixinEval T H A)
  : ! WellFormedMixinEval F (G + H) T A.
Proof.
  constructor.
  intros rec e.
  unfold evalMixinAlgebra.
  unfold MixinEvalSum1.
  apply wellFormedMixinEval.
Defined.

Global Instance WellFormedMixinEvalRight
       `{FF : Functor F} `{FH : Functor H}
       `{MFA : ! MixinEval T F A}
       `{MHA : ! MixinEval T H A}
       `{S : F <= H}
       `(WF : ! WellFormedMixinEval MFA MHA S)
       `{FG : Functor G}
       `(GA : ! MixinEval T G A)
  : ! WellFormedMixinEval F (G + H) T A.
Proof.
  constructor.
  intros rec e.
  unfold evalMixinAlgebra.
  unfold MixinEvalSum1.
  apply wellFormedMixinEval.
Defined.
