module practice2 where

open import Data.Nat
open import Data.List
open import Data.Bool

_<'_ : ℕ → ℕ → Bool
n <' 0 = false
0 <' _ = true
suc(n) <' suc(m) = n <' m

lookup : {A : Set}  (xs : List A) → (ix : ℕ) → T (ix <' (length xs)) → A
lookup (x ∷ xs) zero unit = x
lookup (x ∷ xs) (suc n) unit = lookup xs n unit
lookup [] ix ()


