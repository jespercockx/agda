
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data A : Set where
  a : A

mutual

  data S : Set where
    c : (s : S) (x : A) → f s ≡ x → S

  f : S → A
  f (c _ x _) = x

{-# TERMINATING #-}
foo : S
foo = c foo a {!refl!}
