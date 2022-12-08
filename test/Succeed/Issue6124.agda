open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

id : (@0 A : Set) → A → A
id _ x = x

macro
  @0 testReduceM : Term → TC ⊤
  testReduceM goal = do
    t ← inferType (def (quote id) [])
    _ ← reduce t
    unify goal (def (quote ⊤) [])

testReduce : Set
testReduce = testReduceM

macro
  testUnifyM : Term → TC ⊤
  testUnifyM hole = getType (quote _,_) >>= unify hole

testUnify : Setω
testUnify = testUnifyM
