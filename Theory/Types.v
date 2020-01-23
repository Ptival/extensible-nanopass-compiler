From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

(** [TypeFix] is just an alias for [UniversalPropertyF], but it makes it so that
    code that depends on wrapping types can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition TypeFix LT `{FunctorLaws LT}
  := UniversalPropertyF LT.

Definition TypeOfResult
           LT `{FunctorLaws LT}
  := option (TypeFix LT).

Variant TypeOf := .

Definition typeOf
           {L LT}
           `{FunctorLaws L} `{FunctorLaws LT}
           {TypeOfL : forall T, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
  : Fix L -> TypeOfResult LT
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ _ (TypeOfL _)).

Definition TypeEqualityResult
           LT `{FunctorLaws LT}
  := TypeFix LT -> bool.

Variant TypeEquality := .

Definition typeEquality
           LT `{FunctorLaws LT}
           {typeEqualityForLT : forall T, ProgramAlgebra TypeEquality LT T (TypeEqualityResult LT)}
  : Fix LT -> TypeEqualityResult LT
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ _ (typeEqualityForLT _)).
