
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

postulate @0 X : Set

@0 tricky : Σ Set (X ≡_)
tricky = X , refl

macro
  testM : Term → TC ⊤
  testM hole = do
    (X' , refl) ← unquoteTC {A = Σ Set (X ≡_)} (def (quote tricky) [])
    returnTC _