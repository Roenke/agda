{-# OPTIONS --without-K #-}

module tasks10 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_)
open import lect10

-- 1. Докажите, что (n + m)-элементное множество равно размеченному объединению n- и m-элементного.


open ≡-Reasoning

Fin-sum : (n m : ℕ) → Fin (n + m) ≡ (Fin n ⊎ Fin m)
Fin-sum n m = SetExt ((λ x → {!!}) , ((λ x → {!!}) , {!!}))
-- 2. Докажите, что тип равенств между множествами хоть и не является утверждением, но является множеством.

Set-isGpd : (A B : Set) → isSet (A ≡ B)
Set-isGpd A B with (SmallTypesAreSets A)
Set-isGpd A B | p with (SmallTypesAreSets B)
Set-isGpd A B | p₁ | p₂ = λ x y x₁ y₁ → {!!}

-- 3. Докажите, что аксиома K не выполняется для множеств.

K : ∀ {l} → Set l → Set l
K A = (a : A) (p : a ≡ a) → p ≡ refl

K-is-false : K Set → ⊥
K-is-false k =
  let t = k Bool (SetExt (not , (not , not-not , not-not)))
  in ? -- subst {!!} {!!} {!!}
-- 4. Докажите, что inv является обратным к **.

inv-left : {A : Set} {x y : A} (p : x ≡ y) → inv p ** p ≡ idp
inv-left refl = refl

inv-right : {A : Set} {x y : A} (p : x ≡ y) → p ** inv p ≡ idp
inv-right refl = refl

-- 5. Для любого группоида A постройте группу автоморфизмов его элемента a : A.

record Group (A : Set) : Set where
  field
    set : isSet A
    id : A
    _&_ : A → A → A
    ginv : A → A
    assoc : {x y z : A} → (x & y) & z ≡ x & (y & z)
    id-left : {x : A} → id & x ≡ x
    id-right : {x : A} → x & id ≡ x
    ginv-left : {x : A} → ginv x & x ≡ id
    ginv-right : {x : A} → x & ginv x ≡ id

aut : {A : Set} → isGpd A → (a : A) → Group (a ≡ a)
aut = {!!}

-- 6. Докажите, что множество автоморфизмов 2-х элементного множества состоит из двух элементов.

data Bool₁ : Set₁ where
  true false : Bool₁

aut-Bool : (Bool ≡ Bool) ≡ Bool₁
aut-Bool = {!!}

-- 7. Докажите, что группа автоморфизмов в общем случае не коммутативна.

_**'_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p **' refl = p

aut-is-not-comm : ((A : Set) (p q : A ≡ A) → p **' q ≡ q **' p) → ⊥
aut-is-not-comm = {!!}

-- 8. Докажите, что isProp является предикатом.

isProp-isProp : {A : Set} → isProp (isProp A)
isProp-isProp = {!!}
