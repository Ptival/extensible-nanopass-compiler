From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Functor
.

Declare Scope Sum1.
Delimit Scope Sum1 with Sum1.
Local Open Scope Sum1.

Variant Sum1 (F G : Set -> Set) (A : Set) : Set :=
| inl1 : F A -> (F + G)%Sum1 A
| inr1 : G A -> (F + G)%Sum1 A
where
"F + G" := (Sum1 F G) : Sum1.
Arguments inl1 {F G A}.
Arguments inr1 {F G A}.

Global Instance Functor_Sum1
       {F G} `{Functor F} `{Functor G}
  : Functor (F + G).
Proof.
  refine
    {|
      fmap := fun A B f fga =>
                match fga with
                | inl1 fa => inl1 (fmap f fa)
                | inr1 ga => inr1 (fmap f ga)
                end;
    |}.
  - move => A [] ?; rewrite fmapId => //.
  - move => A B C f g [] ?; rewrite fmapFusion //.
Defined.

Definition sum1Dispatch {A} {L R : Set -> Set} {O} (fl : L A -> O) (fr : R A -> O) v :=
  match v with
  | inl1 l => fl l
  | inr1 r => fr r
  end.
Notation "f || g" := (sum1Dispatch f g) : Sum1.
