
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

data Zero : Set where

data One : Set where
  void : One

propLT : Nat -> Nat -> Set
propLT zero    m       = One
propLT (suc n) zero    = Zero
propLT (suc n) (suc m) = propLT n m

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toFin : {n : Nat} -> (i : Nat) -> (propLT (suc i) n) -> Fin n
toFin {zero} i ()
toFin {suc n} zero void = fzero
toFin {suc n} (suc i) k = fsuc (toFin i k)

bug : Fin (suc zero)
bug = toFin zero void
