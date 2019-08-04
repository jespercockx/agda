{-# OPTIONS --type-in-type -v tc.meta.check:30 -v tc.meta.assign:10 -v tc.meta.blocked:30 -v tc.meta.new:50 -v tc.conv:50 -v tc.constr.solve:50 -v tc.constr.blocked:50 #-}

data _≡_ {A : Set} (x : A) : A → Set where
  instance refl : x ≡ x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ
infixr 4 _,_

postulate whatever : {A : Set} → A

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

data U : Set where
  el : Set → U

El : U → Set
El (el A) = A

data Ctxt : Set
Env : Ctxt → Set

data Ctxt where snoc : (G : Ctxt) → (Env G → U) → Ctxt
Env (snoc G s) = Σ (Env G) (λ g → El (s g))

Var : (G : Ctxt) → (Env G → U) → Set
Var (snoc G s) t = Either ((λ g → s (fst g)) ≡ t) (Σ (Env G → U) (λ u → Σ ((λ g → u (fst g)) ≡ t) (λ _ →  Var G u)))

lookup : (G : Ctxt) (s : Env G → U) → Var G s → (g : Env G) → El (s g)
lookup (snoc vs v) _ (left refl) g = snd g
lookup (snoc vs v) _ (right (_ , refl , x)) g = lookup _ _ x (fst g)

myctxt = (snoc (snoc whatever (λ _ → el Set)) (λ g → el (snd g)))

postulate
  Type : (G : Ctxt) (s : Env G → U) → Set
  suc : (G : Ctxt) (s : Env G → U) (t : Env G → U) → Var (snoc G s) (λ g → t (fst g))
  el' : (G : Ctxt) (x : Var G (λ _ → el Set)) → Type G (λ g → el (lookup G (λ _ → (el Set)) x g))

test :  Type myctxt (λ g → el (snd (fst g)))
test = el' _ (((suc _ (λ z → el (snd z)) _)))
