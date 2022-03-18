
open import Agda.Primitive
open import Agda.Builtin.Equality

data Empty : Set where

record ⊥ : Set where
  field .irr : Empty
open ⊥ public

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

≢-sym : ∀ {a} {A : Set a} {x y : A} → (x ≡ y → ⊥) → (y ≡ x → ⊥)
≢-sym x≢y = x≢y ∘ sym

{-———— Errors ————————————————————————————————————————————————
Failed to solve the following constraints:
  a = _a_42 (x≢y = (λ z → record { irr = _ })) (blocked on _a_42)
  _a_42 (x≢y = (λ z → record { irr = _ })) = a (blocked on _a_42)
-}
