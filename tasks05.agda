module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- 1. Используя тип List, определите тип данных (через зависимые записи) списков длины n (число должно быть параметром записи).
--    Реализуйте для такого типа функции head и tail.

list-len : {A : Set} → List A → ℕ
list-len [] = zero
list-len (x ∷ xs) = suc (list-len xs)

record ListN (A : Set) (n : ℕ) : Set where
  constructor lst
  field
    list : List A
    len-eq-n : (list-len list) ≡ n

headN : {A : Set} {n : ℕ} → ListN A (suc n) → A
headN (lst [] ())  
headN (lst (x ∷ _) _) = x

tailN : {A : Set} {n : ℕ} → ListN A (suc n) → ListN A n
tailN (lst [] ())
tailN (lst (_ ∷ xs) _) = lst xs {!!}

-- 2. Определите тип (через зависимые записи) четных натуральных чисел.
--    Определите функцию деления на 2.

isEven : ℕ → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc x)) = isEven x

record Evenℕ : Set where
  constructor evenNum
  field
    num : ℕ
    even : T (isEven num)

div2 : Evenℕ → ℕ
div2 (evenNum (suc zero) ())
div2 (evenNum (zero) _) = zero
div2 (evenNum (suc (suc n)) p) = suc (div2 (evenNum n p))

-- 3. Постройте структуру моноида на типе натуральных чисел (т.е. нужно сконструировать элемент соответствующей записи).

record Monoid : Set₁ where
  field
    A : Set
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

+-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc zero _ _ = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)

id-left' : (n : ℕ) → 0 + n ≡ n
id-left' n = refl

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))

open ≡-Reasoning

id-right' : (n : ℕ) → n + 0 ≡ n
id-right' n =
  begin
    n + 0
  ≡⟨ +-comm n 0 ⟩
    0 + n
  ≡⟨ refl ⟩
    n
  ∎

ℕ-Monoid : Monoid
ℕ-Monoid =  record
              { A = ℕ
              ; id = 0
              ; _#_ = _+_
              ; assoc = +-assoc
              ; id-left = id-left'
              ; id-right = id-right'
              }

-- 4. Напишите тип монады (через зависимые записи).
--    Элементы этого типа должны удовлетворять всем законом монад.

record Monad (M : Set → Set) : Set₁ where
  field
    return : {A : Set} → A → M A
    _>>=_ : {A B : Set} → M A → (A → M B) → M B

    left-id : {A B : Set} (a : A) (f : A → M B) → (return a) >>= f ≡ f a
    right-id : {A : Set} (m : M A) → m >>= return ≡ m
    assoc : {A B C : Set} (m : M A) (f : A → M B) (g : B → M C) → (m >>= f) >>= g ≡ (m >>= (λ x → f x >>= g))
  
-- 5. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

fmap-maybe : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap-maybe f nothing = nothing
fmap-maybe f (just x) = just (f x)

fmap-maybe-id : {A : Set} (a : Maybe A) → fmap-maybe (λ x → x) a ≡ a
fmap-maybe-id nothing = refl
fmap-maybe-id (just x) = refl

fmap-maybe-comp : {A B C : Set} (f : A → B) (g : B → C) (a : Maybe A) → fmap-maybe (λ x → g (f x)) a ≡ fmap-maybe g (fmap-maybe f a)
fmap-maybe-comp f g nothing = refl
fmap-maybe-comp f g (just x) = refl

Maybe-Functor : Functor Maybe
Maybe-Functor = record
                { fmap = fmap-maybe
                ; fmap-id = fmap-maybe-id
                ; fmap-comp = fmap-maybe-comp
                }

maybe-bind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
maybe-bind nothing _ = nothing
maybe-bind (just x) f = f x

maybe-right-id : {A : Set} (m : Maybe A) → maybe-bind m just ≡ m
maybe-right-id nothing = refl
maybe-right-id (just _) = refl

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
_>>=_ = maybe-bind
maybe-assoc : {A B C : Set} (m : Maybe A) (f : A → Maybe B) (g : B → Maybe C) → (m >>= f) >>= g ≡ (m >>= (λ x → f x >>= g))
maybe-assoc nothing f g = refl 
maybe-assoc (just _) f g = refl

Maybe-Monad : Monad Maybe
Maybe-Monad = record
                { return = just 
                ; _>>=_ = maybe-bind
                ; left-id = λ a f → refl
                ; right-id = maybe-right-id
                ; assoc = maybe-assoc
                }

-- 6. Реализуйте sscanf.
