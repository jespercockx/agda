
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.List

macro
  testM : Term → TC ⊤
  testM hole = unify hole (var 0 [])

test : @0 Set → Set
test A = testM
