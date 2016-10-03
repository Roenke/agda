module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- 1. Используя тип List, определите тип данных (через зависимые записи) списков длины n (число должно быть параметром записи).
--    Реализуйте для такого типа функции head и tail.

-- 2. Определите тип (через зависимые записи) четных натуральных чисел.
--    Определите функцию деления на 2.

record Evenℕ : Set where

div2 : Evenℕ → ℕ
div2 = {!!}

-- 3. Постройте структуру моноида на типе натуральных чисел (т.е. нужно сконструировать элемент соответствующей записи).

record Monoid : Set₁ where
  field
    A : Set
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

ℕ-Monoid : Monoid
ℕ-Monoid = {!!}

-- 4. Напишите тип монады (через зависимые записи).
--    Элементы этого типа должны удовлетворять всем законом монад.

record Monad (M : Set → Set) : Set₁ where

-- 5. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where

Maybe-Functor : Functor Maybe
Maybe-Functor = {!!}

Maybe-Monad : Monad Maybe
Maybe-Monad = {!!}

-- 6. Реализуйте sscanf.
