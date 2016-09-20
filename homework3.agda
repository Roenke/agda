module homework3 where

open import Data.Nat
open import Data.Unit
open import Data.Product

vec : Set → ℕ → Set
vec A 0 = ⊤
vec A (suc n) = A × vec A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- 1. Реализуйте аналоги функции map для vec и Vec.

map-Vec : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
map-Vec _ nil = nil
map-Vec fun (cons x xs) = cons (fun x) (map-Vec fun xs)

map-vec : {A B : Set} {n : ℕ} → (A → B) → vec A n → vec B n
map-vec {a} {b} {0} _ _ = tt
map-vec {a} {b} {suc n} fun (x , xs) = (fun x , map-vec fun xs)

-- 2. Реализуйте аналоги функции zip для vec и Vec.

zip-vec : {A B : Set} {n : ℕ} → vec A n → vec B n → vec (A × B) n
zip-vec {_} {_} {0} _ _ = tt
zip-vec {_} {_} {suc n} (x , xs) (y , ys) = ((x , y) , (zip-vec xs ys))

zip-Vec : {A B : Set} {n : ℕ} → Vec A n → Vec B n → Vec (A × B) n
zip-Vec nil nil = nil
zip-Vec (cons x xs) (cons y ys) = cons (x , y) (zip-Vec xs ys)

-- 3. Функции Fin n → A соответствуют спискам элементов A длины n.
--    Функция, преобразующие Vec A n в Fin n → A была реализована на лекции.
--    Реализуйте обратную функцию.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

coin : {A : Set} {n : ℕ} → (Fin n → A) → Vec A n
coin {_} {0} f = nil
coin {_} {suc n} f = {!!} --cons (f (zero)) (coin f)

-- 4. Определите тип матриц и ряд функций над ними.

Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n

m : Mat ℕ 2 2
m = cons (cons 0 (cons 1 nil)) (cons (cons 2 (cons 3 nil)) nil) 
mt = cons (cons 0 (cons 2 nil)) (cons (cons 1 (cons 3 nil)) nil) 

-- диагональная матрица

repeat : {A : Set} → A → (n : ℕ) → Vec A n
repeat _ 0 = nil
repeat val (suc n) = cons val (repeat val n) 

ins-begin : {A : Set} {n m : ℕ} → A → Mat A n m → Mat A n (suc m)
ins-begin _ nil = nil
ins-begin v (cons l ls) = cons (cons v l) (ins-begin v ls)

diag-acc : {A : Set} {n m r : ℕ} → ℕ → Mat A r r → A → Mat A r r
diag-acc 0 acc _ = acc
diag-acc (suc n) acc (cons l ls)

diag : {A : Set} → A → A →{n : ℕ} → Mat A n n
diag val z {0} = nil
diag val z {suc n} = ? -- cons (cons val (repeat z n)) (ins-begin z 

-- транспонирование матриц

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose M = {!!} 

-- сложение матриц

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ M N = {!!}

-- умножение матриц

mul : {A : Set} (_+_ _*_ : A → A → A) → {n m k : ℕ} → Mat A n m → Mat A m k → Mat A n k
mul _+_ _*_ M N = {!!}

-- 5. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

data CTree (A : Set) : ℕ → Set where

-- 6. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.

data Tree (A : Set) : ℕ → Set where

-- определите функцию, возвращающую высоту дерева.

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height n t = {!!}
