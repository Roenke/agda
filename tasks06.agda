module tasks06 where

open import Data.Nat hiding (_<_)
open import Data.List hiding (filter)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product

-- 1. Реализуйте любой алгоритм сортировки, используя with для паттерн матчинга на результате сравнения элементов списка.

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

insert : ℕ → List ℕ → List ℕ
insert val [] = val ∷ []
insert val (x ∷ xs) with (x < val)
insert val (x ∷ xs) | true = val ∷ x ∷ xs
insert val (x ∷ xs) | false = x ∷ (insert val xs)

sort' : List ℕ → List ℕ → List ℕ
sort' acc [] = acc
sort' acc (x ∷ xs) = sort' (insert x acc) xs

sort : List ℕ → List ℕ
sort [] = []
sort xs = sort' [] xs

-- 2. Определите filter через if, а не через with.
--    Докажите для этой версии filter следующую лемму:

filter : {A : Set} → (A → Bool) → List A → List A
filter _ [] = []
filter p (x ∷ xs) = if (p x) then (x ∷ (filter p xs)) else (filter p xs)

lem : {A : Set} (p : A → Bool) (xs : List A) → length (filter p xs) ≤ length xs
lem p [] = z≤n
lem p (x ∷ xs) = {!!}

-- 3. Докажите, что если равенство элементов A разрешимо, то и равенство элементов List A тоже разрешимо.

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

List-Dec : {A : Set} → DecEq A → DecEq (List A)
List-Dec = {!!}

-- 4. Докажите, что предикат isEven разрешим.

DecPred : {A : Set} → (A → Set) → Set
DecPred {A} P = (a : A) → Dec (P a)

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

isEven-Dec : DecPred isEven
isEven-Dec = {!!}

-- 5. Докажите, что если равенство элементов A разрешимо, то любой список элементов A либо пуст, либо состоит из повторений одного элемента, либо в A существует два различных элемента.

repeat : {A : Set} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

data Result (A : Set) (xs : List A) : Set where
  empty : xs ≡ [] → Result A xs
  repeated : (n : ℕ) (a : A) → xs ≡ repeat n a → Result A xs
  A-is-not-trivial : (a a' : A) → ¬ (a ≡ a') → Result A xs

lemma : {A : Set} (xs : List A) → DecEq A → Result A xs
lemma = {!!}

-- 6. Определите view, представляющий число в виде частного и остатка от деления его на произвольное (неотрицательное) число m.
--    Реализуйте функцию деления.

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

mod-view : (m n : ℕ) → T (isPos m) → ModView m n
mod-view = {!!}

div : ℕ → (m : ℕ) → T (isPos m) → ℕ
div n m p = {!!}
