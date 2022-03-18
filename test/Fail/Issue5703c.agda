{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

postulate
  @0 A : Set
  B : Set

C : Bool → Set → Set
C true  X = X
C false _ = B

mutual
  Z : Bool → Set
  Z = _

  unsolved : {b : Bool} → Z b ≡ C b A
  unsolved = refl
