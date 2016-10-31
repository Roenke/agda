{-# OPTIONS --without-K #-}

module tasks09 where

open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat

open import Trunc

-- 1. Докажите следующие правила, характеризующие квантор существования.

∃ : (A : Set) (B : A → Set) → Set
∃ A B = ∥ Σ A B ∥

∃-intro : {A : Set} {B : A → Set} → (a : A) → B a → ∃[ x ∶ A ] (B x)
∃-intro a b = ∣ a , b ∣

∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃ A B → C
∃-elim propC toC ex = Trunc-rec propC (λ{ (a , b) → toC a b})  ex

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

-- 2. Определите утверждение "натуральные числа существуют".

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

natural-numbers-exist : hProp
natural-numbers-exist = prop ℕ (λ x y → {!!})

-- 3. Докажите, что функция pred сюръективна.

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

pred-is-sur : isSur pred
pred-is-sur = {!!}

-- 4. Докажите, что функция suc не сюръективна.

suc-is-not-sur : isSur suc → ⊥
suc-is-not-sur = {!!}

-- 5. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g сюръективны, то g ∘ f также сюръективна.
--    Докажите, что если g ∘ f сюръективна, то g также сюръективна.

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

∘-sur : {A B C : Set} (f : A → B) (g : B → C) → isSur f → isSur g → isSur (g ∘ f)
∘-sur = {!!}

∘-sur' : {A B C : Set} (f : A → B) (g : B → C) → isSur (g ∘ f) → isSur g
∘-sur' = {!!}

-- 6. Докажите, что функция является биекцией тогда и только тогда, когда она является инъекцией и сюръекцией.

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij : {A B : Set} → (A → B) → Set
isBij {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

isBij-isInj : {A B : Set} (f : A → B) → isBij f → isInj f
isBij-isInj = {!!}

isBij-isSur : {A B : Set} (f : A → B) → isBij f → isSur f
isBij-isSur = {!!}

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

-- Эта лемма вам может пригодится
sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} (p : a ≡ a') → subst B p b ≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl q = cong (_,_ _) q

isInj-isSur-isBij : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → isBij f
isInj-isSur-isBij = {!!}

-- 7. Докажите, что isBij является утверждением.

isBij-isProp : {A B : Set} → isSet A → isSet B → (f : A → B) → isProp (isBij f)
isBij-isProp = {!!}

-- 8. См. Cantor.agda.
