

data A : Set where
  a : A

data B : A → Set where
  b : B a

mutual

  a′ : A
  a′ = {!f b!}

  f : B a′ → A
  f b = a
