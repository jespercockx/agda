{-# OPTIONS --cubical-compatible #-}
postulate
  A : Set
  B : A → Set

-- Jesper, 2022-12-08: I do not see a reason why this should be
-- rejected. The @0 says that the argument x should not be used in the
-- *body* of the function, but it should be fine to use it in the
-- *codomain*.

T = (@0 x : A) → B x
