module practice4 where

open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Data.Sum
open import Data.Vec hiding (reverse) renaming (_++_ to _+V+_)
open import Data.List hiding (reverse) renaming (_++_ to _+L+_)
open import Relation.Binary.PropositionalEquality hiding (sym; trans; cong; cong₂)
open import Data.Bool
open import Data.Unit
-- 2. Определите симметричность, транзитивность и конгруэнтность при помощи паттерн матчинга.

sym : {A : Set} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

cong : {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl


-- 1. Доказать следующий факт.

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

_==_ : (ℕ → ℕ) → (ℕ → ℕ) → Set
f == g = (x : ℕ) → f x ≡ g x

D : ℕ → Set
D zero = ⊥
D (suc _) = ⊤

infix 1 _=='_
_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' suc _ = false
suc _ ==' 0 = false
suc x ==' suc y = x ==' y

≡-== : (x y : ℕ) → x ≡ y → T (x ==' y)
≡-== zero zero p = tt
≡-== zero (suc y) ()
≡-== (suc x) zero p = subst D p tt
≡-== (suc x) (suc y) p = ≡-== x y (cong pred p)

lem : fac == suc → ⊥
lem p = ≡-== (suc zero) (suc (suc zero)) (p 1)

-- 3. Определите конгруэнтность для функций двух аргументов через subst.

cong₂ : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f {a = a} {b = b} {b' = b'} pa pb = subst (λ x → f a b ≡ f x b') pa (subst (λ x → f a b ≡ f a x) pb refl)

-- 4. Докажите дистрибутивность умножения над сложением для натуральных чисел.

open ≡-Reasoning

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc zero = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))

distr : (n m k : ℕ) → n * (m + k) ≡ n * m + n * k
distr zero _ _ = refl
distr (suc n) m k =
  (begin
    (suc n) * (m + k)
  ≡⟨ refl ⟩
    (m + k) + n * (m + k)
  ≡⟨ {!!} ⟩
    (m + n * m) + (k + n * k)
  ≡⟨ refl ⟩
    (suc n) * m + (suc n) * k
  ∎)

-- 5. Докажите следующее утверждение.

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs +L+ x ∷ []

reverse-inv : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-inv = {!!}

-- 6. Докажите следующее утверждение.

reverse-append : {A : Set} (xs ys : List A) → reverse (xs +L+ ys) ≡ reverse ys +L+ reverse xs
reverse-append = {!!}

-- 7. Докажите, что [] является нейтральным элементом для ++.

[]-is-neutral : {A : Set} {n : ℕ} (xs : Vec A n) → subst (Vec A) (+-comm n 0) (xs +V+ []) ≡ xs
[]-is-neutral xs = {!!}

-- 8. Определите reverse для Vec через аккумулятор.

rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev = {!!}

-- 9. Докажите, что [] не равно x ∷ xs при помощи паттер матчинга.

List-diff : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff = {!!}

-- 10. Докажите, что [] не равно x ∷ xs при помощи subst.

List-diff' : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff' = {!!}
