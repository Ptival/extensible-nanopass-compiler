From ExtensibleCompiler.Theory Require Import IndexedFunctor.

Delimit Scope IndexedSum1_scope with IndexedSum1.
Open Scope IndexedSum1_scope.

Variant IndexedSum1 I (F G : I-indexedProp) (A : I -> Prop) (i : I) : Prop :=
| iinl1 : F A i -> (F + G)%IndexedSum1 A i
| iinr1 : G A i -> (F + G)%IndexedSum1 A i
where "F + G" := (IndexedSum1 _ F G) : IndexedSum1_scope.
Arguments iinl1 {I F G A i}.
Arguments iinr1 {I F G A i}.

Global Instance IndexedFunctorSum1
       {I} {F G : I-indexedProp} `{IndexedFunctor I F} `{IndexedFunctor I G}
  : IndexedFunctor I (F + G)
  | 0 :=
  {|
    ifmap
    := fun A B i f fg =>
         match fg with
         | iinl1 fa => iinl1 (ifmap i f fa)
         | iinr1 ga => iinr1 (ifmap i f ga)
         end;
  |}.

Definition indexedSum1Dispatch
           {I} {A : I -> Prop} {L R : I-indexedProp} {O : I -> Prop} {i}
           (fl : L A i -> O i) (fr : R A i -> O i) v :=
  match v with
  | iinl1 l => fl l
  | iinr1 r => fr r
  end.

Notation "f || g" := (indexedSum1Dispatch f g) : IndexedSum1_scope.
