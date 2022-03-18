
open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

private
  variable
    a : Level
    A B : Set a
    m n o : Nat

postulate w/e : A

data Empty : Set where

record ⊥ : Set where
  field .irr : Empty

postulate
  ⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever

postulate
  cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc  : (i : Fin n) → Fin (suc n)

variable i j : Fin n

toℕ : Fin n → Nat
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

postulate
  suc-injective : Fin.suc i ≡ suc j → i ≡ j

lower₁ : ∀ (i : Fin (suc n)) → (n ≡ toℕ i → ⊥) → Fin n
lower₁ {zero}  zero    ne = ⊥-elim (ne refl)
lower₁ {suc n} (suc i) ne = suc (lower₁ i λ x → ne (cong suc x))
lower₁ _ _ = w/e

lower₁-injective : ∀ {n≢i : n ≡ toℕ i → ⊥} → lower₁ i n≢i ≡ lower₁ i n≢i → ⊥
lower₁-injective {suc n} {suc i} {n≢i} eq =
  lower₁-injective {n} {i} {n≢i = _} (suc-injective eq)
{-                                ^
    Unsolved metavariable: _n≢i_102 : n ≡ toℕ i → ⊥
-}
lower₁-injective _ = w/e
