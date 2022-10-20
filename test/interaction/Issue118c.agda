
data C : Set where
  c : C

data A : Set₁ where
  _∋_ : (X : Set) → X → A

Dom : A → Set
Dom (X ∋ x) = X

e = {!Dom e!} ∋ c  -- the hole has been instantiated to C
                   -- filling it with Dom e just checks that
                   -- Dom e == C, which is true.
