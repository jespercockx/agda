{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality

postulate
  @0 A : Set
  F : Set → Set

mutual
  X : Set
  X = _

  unsolved : X ≡ F A
  unsolved = refl
  -- Failed to solve the following constraints:
  --  _3 = F A : Set (blocked on _3)
