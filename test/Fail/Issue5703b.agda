{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality

postulate
  @0 A : Set
  F : Set → Set

mutual
  Y : @0 Set → Set
  Y A = _

  unsolved : (A : Set) → Y A ≡ F A
  unsolved A = refl
