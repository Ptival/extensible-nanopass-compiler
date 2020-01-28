# Where to start?

## [Eval](./Eval)

Contains evaluation semantics for each feature as a function.

## [EvalRelation](./EvalRelation)

Contains evaluation semantics for each feature as a relation.

## [Soundness](./Soundness)

Contains extensible type soundness proofs for all features, making sure that the
evaluation semantics in [Eval](./Eval) agree with the typing semantics in
[WellTyped](../Static/WellTyped).

## [All](./All)

Each file exports all the above dynamic semantics for a given feature.
