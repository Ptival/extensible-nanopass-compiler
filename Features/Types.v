From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

(** [TypeFix] is just an alias for [UniversalPropertyF], but it makes it so that
    code that depends on wrapping types can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition TypeFix (LT : Set -> Set) `{Functor LT}
  := UniversalPropertyF LT.

Definition TypeOfResult
           (LT : Set -> Set) `{Functor LT}
  := option (TypeFix LT).

Definition typeOf
           L `{Functor L}
           (LT : Set -> Set) `{Functor LT}
           {TypeOfL : forall T, ProgramAlgebra L T (TypeOfResult LT)}
  : Fix L -> TypeOfResult LT
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ (TypeOfL _)).

Definition TypeEqualityResult
           (LT : Set -> Set) `{Functor LT}
  := TypeFix LT -> bool.

Definition typeEquality
           (LT : Set -> Set) `{Functor LT}
           {typeEqualityForLT : forall T, ProgramAlgebra LT T (TypeEqualityResult LT)}
  : Fix LT -> TypeEqualityResult LT
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ (typeEqualityForLT _)).
