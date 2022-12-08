module _ where

module M (A : Set) where

_ : {@0 A : Set} → let open M A in Set₁
_ = Set
