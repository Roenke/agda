module tasks06 where

open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
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
filter p (x ∷ xs) = if (p x)  then (x ∷ (filter p xs)) else (filter p xs)

lem : {A : Set} (p : A → Bool) (xs : List A) → length (filter p xs) ≤ length xs
lem p [] = z≤n
lem p (x ∷ xs) with p x 
lem p (x ∷ xs) | true = s≤s (lem p xs)
lem p (x ∷ xs) | false = ≤-step (lem p xs)

-- 3. Докажите, что если равенство элементов A разрешимо, то и равенство элементов List A тоже разрешимо.

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

head : {A : Set} → (xs : List A) → T (0 < length xs) → A
head [] ()
head (x ∷ xs) _ = x

head' : {A : Set} → A → List A → A
head' def [] = def
head' _ (x ∷ xs) = x

proof : {A : Set} (x y : A) (xs ys : List A) → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
proof x y xs ys = cong (head' x)

tail : {A : Set} → List A → List A
tail [] = []
tail (x ∷ xs) = xs

proof' : {A : Set} (x y : A) (xs ys : List A) → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
proof' x y xs ys = cong tail

proof'' : {A : Set} (x y : A) (xs ys : List A) → x ≡ y → xs ≡ ys → (x ∷ xs) ≡ (y ∷ ys)
proof'' x .x xs .xs refl refl = refl

List-Dec : {A : Set} → DecEq A → DecEq (List A)
List-Dec _ [] [] = yes refl
List-Dec _ [] (y ∷ ys) = no (λ ())
List-Dec _ (x ∷ xs) [] = no (λ ())
List-Dec eq (x ∷ xs) (y ∷ ys) with eq x y | List-Dec eq xs ys
List-Dec eq (x ∷ xs) (y ∷ ys) | yes p | yes p₁ = yes (proof'' x y xs ys p p₁)
List-Dec eq (x ∷ xs) (y ∷ ys) | yes p | no ¬p = no (λ q → ¬p (proof' x y xs ys q))
List-Dec eq (x ∷ xs) (y ∷ ys) | no ¬p | yes p = no (λ q → ¬p (proof x y xs ys q))
List-Dec eq (x ∷ xs) (y ∷ ys) | no ¬p | no ¬p₁ = no (λ q → ¬p (proof x y xs ys q))

-- 4. Докажите, что предикат isEven разрешим.

DecPred : {A : Set} → (A → Set) → Set
DecPred {A} P = (a : A) → Dec (P a)

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

data Nat : ℕ → Set where
  even : (k : ℕ) → Nat (k * 2)
  odd : (k : ℕ) → Nat (suc (k * 2))

toNat : (n : ℕ) → Nat n
toNat 0 = even 0
toNat (suc 0) = odd 0
toNat (suc x) with toNat x
toNat (suc .(k * 2)) | even k = odd k
toNat (suc .(suc (k * 2))) | odd k = even (suc k)

isEven-Dec : DecPred isEven
isEven-Dec n with toNat n
isEven-Dec .(k * 2) | even k = yes (k , refl)
isEven-Dec .(suc(k * 2)) | odd k = no (λ x → proof-neg (proj₁ x) k (proj₂ x) ) where
  proof-neg : (n m : ℕ) → ¬(suc(m * 2) ≡  n * 2)
  proof-neg 0 m ()
  proof-neg (suc n) 0 ()
  proof-neg (suc n) (suc m) p = proof-neg n m (cong (λ x → pred (pred x)) p)
-- 5. Докажите, что если равенство элементов A разрешимо, то любой список элементов A либо пуст, либо состоит из повторений одного элемента, либо в A существует два различных элемента.

repeat : {A : Set} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

data Result (A : Set) (xs : List A) : Set where
  empty : xs ≡ [] → Result A xs
  repeated : (n : ℕ) (a : A) → xs ≡ repeat n a → Result A xs
  A-is-not-trivial : (a a' : A) → ¬ (a ≡ a') → Result A xs

lemma : {A : Set} (xs : List A) → DecEq A → Result A xs
lemma [] _ = empty refl
lemma (x ∷ xs) eq with lemma xs eq
lemma (x ∷ xs) eq | empty p = repeated 1 x (proof'' x x xs [] refl p) 
lemma (x ∷ xs) eq | repeated n e p with eq x e
lemma (x ∷ xs) eq | repeated n e p | yes pr = repeated (1 + n) e (proof'' x e xs (repeat n e) pr p)
lemma (x ∷ xs) eq | repeated n e p | no ¬pr = A-is-not-trivial x e ¬pr
lemma (x ∷ xs) eq | A-is-not-trivial x1 x2 p = A-is-not-trivial x1 x2 p

-- 6. Определите view, представляющий число в виде частного и остатка от деления его на произвольное (неотрицательное) число m.
--    Реализуйте функцию деления.

open import Data.Unit

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

data Ordered : ℕ → ℕ → Set where
  lt : ∀ n m → T (n < m) → Ordered n m
  eq : ∀ n m → n ≡ m → Ordered n m
  gt : ∀ n m → T (m < n) → Ordered n m

order : (n m : ℕ) → Ordered n m
order 0 0 = eq 0 0 refl
order 0 (suc x) = lt 0 (suc x) tt
order (suc x) 0 = gt (suc x) 0 tt
order (suc x) (suc y) with order x y
order (suc x) (suc y) | lt .x .y p = lt (suc x) (suc y) p
order (suc x) (suc y) | eq .x .y p = eq (suc x) (suc y) (cong suc p)
order (suc x) (suc y) | gt .x .y p = gt (suc x) (suc y) p

open ≡-Reasoning

lemma1 : (m q r : ℕ) → r ≡ m → suc(m + q * suc m) ≡ suc (r + q * suc m)
lemma1 m q r p = cong suc (begin 
    m + q * suc m
  ≡⟨ cong (λ x → x + q * suc m) (sym p) ⟩
    r + q * suc m
  ∎)

lemma2 : (m r : ℕ) → T (m < r) → ¬ T (r < suc m) 
lemma2 _ 0 ()
lemma2 0 (suc x) p ()
lemma2 (suc m) (suc r) p1 p2 = lemma2 m r p1 p2

mod-view : (m n : ℕ) → T (isPos m) → ModView m n
mod-view 0 _ ()
mod-view (suc _) 0 p = quot-rem 0 0 p
mod-view (suc m) (suc n) p with mod-view (suc m) n p
mod-view (suc m) (suc .(r + q * (suc m))) p | quot-rem q r p' with order r m
mod-view (suc m) (suc .(r + q * (suc m))) p | quot-rem q r p' | lt .r .m pr = quot-rem q (suc r) pr
mod-view (suc m) (suc .(r + q * (suc m))) p | quot-rem q r p' | eq .r .m pr = subst (ModView (suc m)) (lemma1 m q r pr) (quot-rem (suc q) 0 p)
mod-view (suc m) (suc .(r + q * (suc m))) p | quot-rem q r p' | gt .r .m pr with lemma2 m r pr p'
mod-view (suc m) (suc .(r + q * (suc m))) p | quot-rem q r p' | gt .r .m pr | ()

div : ℕ → (m : ℕ) → T (isPos m) → ℕ
div _ zero ()
div x m p with mod-view m x p
div .(r + q * m) m p | quot-rem q r _ = q
