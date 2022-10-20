{-# OPTIONS --rewriting #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a
{-# BUILTIN REWRITE _==_ #-}

postulate
  A : Set
  a b : A

r : a == b
r = {!idp!}
{-# REWRITE r #-}
