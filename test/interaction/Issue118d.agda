
data C : Set where
  c : C

data A : Set₁ where
  _∋_ : (X : Set) → X → A

Dom : A → Set
Dom (X ∋ x) = X

f = C ∋ c
  where
    g = {!Dom f!} ∋ c
