module practice2 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Unit

-- 2. Определите запись Point, который может хранить элементы произвольных типов A и B произвольных уровней.
--    Определите равенство для такого типа Point.

record Point {level} (A B : Set level) : Set level where
  constructor point
  field
    x : A
    y : B

point-eq : ∀ {level} {A B : Set level}
  (eq-A : A → A → Bool) →
  (eq-B : B → B → Bool) →
  Point A B → Point A B → Bool
point-eq eq-A eq-B (point x1 y1) (point x2 y2) = (eq-A x1 x2) ∧ (eq-B y1 y2)

-- 3. Напишите функцию lookup, которая принимает список и натуральное число и возвращает элемент по заданому индексу.
--    В общем случае эту функцию определить невозможно, т.к. индекс может быть больше, чем число элементов в списке.
--    Поэтому эта функция должна дополнительно еще принимать доказательство того, что всё хорошо.

_<'_ : ℕ → ℕ → Bool
n <' 0 = false
0 <' _ = true
suc(n) <' suc(m) = n <' m

lookup : {A : Set}  (xs : List A) → (ix : ℕ) → T (ix <' (length xs)) → A
lookup (x ∷ xs) zero unit = x
lookup (x ∷ xs) (suc n) unit = lookup xs n unit
lookup [] _ ()

-- 4. Докажите ассоциативность сложения для натуральных чисел.

_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' _ = false
_ ==' zero = false
(suc n) ==' (suc m) = n ==' m

num-refl : (x : ℕ) → T(x ==' x)
num-refl zero = tt
num-refl (suc x) = num-refl x

+assoc : (x y z : ℕ) → T (((x + y) + z) ==' (x + (y + z)))
+assoc zero zero z = num-refl z
+assoc zero y z = num-refl (y + z)
+assoc (suc x) y z = +assoc x y z

-- 5. Обобщите алгоритм сортировки так, чтобы он работал для произвольных типов.
--    Используйте для этого модули.
--    Вызовите этот алгоритм на каком-нибудь списке натуральных чисел. Например, 3 ∷ 1 ∷ 2 ∷ []

module Sort {A : Set} (_<_ : A → A → Bool) where
 
  sort' : ℕ → List A → List A
  sort' zero xs = xs
  sort' _ [] = []
  sort' (suc c) (x ∷ xs)  = ((sort' c lt) ++ (x ∷ [])) ++ (sort' c gt) where
    lt = filter (\p → p < x) xs
    gt = filter (\p → x < p) xs

  elem-eq : A → A → Bool
  elem-eq a b = (not (a < b)) ∧ (not (b < a))

  list-eq : List A → List A → Bool
  list-eq [] [] = true
  list-eq _ [] = false
  list-eq [] _ = false
  list-eq (x ∷ xs) (y ∷ ys) = if (elem-eq x y) then (list-eq xs ys) else false

  sort : List A → List A
  sort xs = sort' (length xs) xs

open Sort _<'_ 

sort-test : T ( list-eq (sort (3 ∷ 1 ∷ 2 ∷ 5 ∷ 0 ∷ 4 ∷ [])) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) )
sort-test = tt
