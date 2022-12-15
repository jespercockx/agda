
record R (A : Set) : Set where
  field
    x : A

open R

shouldwork : (@0 A : Set) → R A → A
shouldwork = λ (@0 A) r → x r
