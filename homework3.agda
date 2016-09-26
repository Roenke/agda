module homework3 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Bool

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
map-vec {n = 0} _ _ = tt
map-vec {n = suc _} fun (x , xs) = (fun x , map-vec fun xs)

-- 2. Реализуйте аналоги функции zip для vec и Vec.

zip-vec : {A B : Set} {n : ℕ} → vec A n → vec B n → vec (A × B) n
zip-vec {n = 0} _ _ = tt
zip-vec {n = suc n} (x , xs) (y , ys) = ((x , y) , (zip-vec xs ys))

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
coin {n = zero} _ = nil
coin {n = suc n} fun = cons (fun zero) (coin (λ x → fun (suc x)))

-- 4. Определите тип матриц и ряд функций над ними.

Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n

m : Mat ℕ 2 2
m = cons (cons 0 (cons 1 nil)) (cons (cons 2 (cons 3 nil)) nil) 
mt = cons (cons 0 (cons 2 nil)) (cons (cons 1 (cons 3 nil)) nil) 

fst : {A B : Set} → A × B → A
fst (x , _) = x

snd : {A B : Set} → A × B → B
snd (_ , y) = y

zipWith : {A B C : Set} {n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _ nil nil = nil
zipWith fun vec₁ vec₂ = map-Vec (λ x → fun (fst x) (snd x)) (zip-Vec vec₁ vec₂) 
-- диагональная матрица

diag : {A : Set} → A → A → {n : ℕ} → Mat A n n
diag z e {zero} = nil
diag z e {suc n} = cons (cons z (coin (λ _ → z)))
  (map-Vec (λ l → cons z l) (diag z e {n}))
-- транспонирование матриц

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose nil = coin (λ _ → nil)
transpose (cons line M) = zipWith cons line (transpose M)

-- сложение матриц

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ nil nil = nil
add _+_ (cons line₁ N) (cons line₂ M) = cons (zipWith _+_ line₁ line₂) (add _+_ N M)

-- умножение матриц

mul : {A : Set} (_+_ _*_ : A → A → A) → {n m k : ℕ} → Mat A n m → Mat A m k → Mat A n k
mul _+_ _*_ M N = {!!}

-- 5. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

data CTree (A : Set) : ℕ → Set where
  leaf : CTree A 0
  node : {n : ℕ} → A × (CTree A n) × (CTree A n) → (CTree A (suc n))
  
-- 6. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.

max : ℕ → ℕ → ℕ
max zero x = x
max x zero = x
max (suc n) (suc m) = suc (max n m)

min : ℕ → ℕ → ℕ
min zero x = zero
min x zero = zero
min (suc n) (suc m) = suc (min n m)


_<'_ : ℕ → ℕ → Bool
zero <' zero = false
zero <' _ = true
_ <' zero = false
(suc n) <' (suc m) = n <' m

_<='_ : ℕ → ℕ → Bool
zero <=' _ = true
_ <=' zero = false
(suc n) <=' (suc m) = n <=' m

data Tree (A : Set) : ℕ → Set where
  leaf : Tree A 0
  left-heavy : {n m : ℕ} →  T(m <=' n) → A × (Tree A n) × (Tree A m) → Tree A (suc n)
  right-heavy : {n m : ℕ} → T(n <' m) → A × (Tree A n) × (Tree A m) → Tree A (suc m)
  --node : {n m : ℕ} → A × (Tree A n) × (Tree A m) → (Tree A (suc (max n m)))
-- определите функцию, возвращающую высоту дерева.

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height zero leaf = zero
height (suc n) (left-heavy _ (_ , t1 , t2)) = suc (height n t1)
height (suc n) (right-heavy _ (_ , t1 , t2)) = suc (height n t2)
