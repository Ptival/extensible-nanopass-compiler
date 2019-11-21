From ExtensibleCompiler.Theory Require Import Functor.

Delimit Scope Sum1_scope with Sum1.
Open Scope Sum1_scope.

Variant Sum1 (F G : Set -> Set) (A : Set) : Set :=
| inl1 : F A -> (F + G)%Sum1 A
| inr1 : G A -> (F + G)%Sum1 A
where
"F + G" := (Sum1 F G) : Sum1_scope.

Arguments inl1 {F G A}.
Arguments inr1 {F G A}.

Global Instance Functor_Sum1
       {F G} `{Functor F} `{Functor G}
  : Functor (F + G)
  | 0 :=
  {|
    fmap := fun A B f fga =>
              match fga with
              | inl1 fa => inl1 (fmap f fa)
              | inr1 ga => inr1 (fmap f ga)
              end;
  |}.

Definition sum1Dispatch {A} {L R : Set -> Set} {O} (fl : L A -> O) (fr : R A -> O) v :=
  match v with
  | inl1 l => fl l
  | inr1 r => fr r
  end.

Notation "f || g" := (sum1Dispatch f g) : Sum1_scope.
