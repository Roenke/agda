module practice3 where

open import Data.Nat
open import Data.Unit
open import Data.Product

-- 1. Define Vec recursively
Vec' : Set → ℕ → Set
Vec' A 0 = ⊤
Vec' A (suc n) = A × (Vec' A n)

list : Vec' ℕ 3
list = 0 , 1 , 2 , tt

head : {A : Set} {n : ℕ} → Vec' A (suc n) → A
head (x , _) = x

-- 2. Define Vec inductively
data List : Set → Set₁ where
  nil : {A : Set} →  List A
  cons : {A : Set} → List A → List A

--data Vec₂ (A : Set) (n : ℕ) : Set where
--  nil : T (n == 0) Vec₂ A n
--  cons : {n' : ℕ} → T (n == suc n') → A → Vec₂ A n → Vec₂ A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

list₀ : Vec ℕ 0
list₀ = nil

list₁ : Vec ℕ 1
list₁ = cons 10 nil

list₂ : Vec ℕ 2
list₂ = cons 11 list₁

-- 3. Define head, tail, append

-- 4. Define length
