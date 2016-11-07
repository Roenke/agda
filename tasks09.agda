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
natural-numbers-exist = prop (∥ ℕ ∥) trunc 

-- 3. Докажите, что функция pred сюръективна.

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

pred-is-sur : isSur pred
pred-is-sur n = ∃-intro (suc n) refl

-- 4. Докажите, что функция suc не сюръективна.

⊥-isProp : isProp ⊥
⊥-isProp = λ x ()

suc-is-not-sur : isSur suc → ⊥
suc-is-not-sur proof = lem (proof zero)
  where
    lem' : (x : ℕ) → (suc x ≡ zero) → ⊥
    lem' _ ()
    lem : ∃[ x ∶ ℕ ] (suc x ≡ zero) → ⊥
    lem p = ∃-elim ⊥-isProp  (λ a x → lem' a x) p
    
-- 5. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g сюръективны, то g ∘ f также сюръективна.
--    Докажите, что если g ∘ f сюръективна, то g также сюръективна.

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

open ≡-Reasoning

∘-trans : {a b c : Set} → (f : a → b) → (g : b → c) → (a : a) → (b : b) → (c : c) → (f a ≡ b) → (g b ≡ c) → ((g ∘ f) a ≡ c)
∘-trans f g a b c p1 p2  =
  begin
    (g ∘ f) a
  ≡⟨ refl ⟩
    g (f a)
  ≡⟨ cong (λ x → g x) p1 ⟩
    g b
  ≡⟨ p2 ⟩
    c
  ∎

∘-sur : {A B C : Set} (f : A → B) (g : B → C) → isSur f → isSur g → isSur (g ∘ f)
∘-sur f g fSur gSur = λ y → ∃-elim trunc (λ a x → ∃-elim trunc (λ a₁ x₁ → ∃-intro a₁ (∘-trans f g a₁ a y x₁ x)) (fSur a)) (gSur y)

∘-sur' : {A B C : Set} (f : A → B) (g : B → C) → isSur (g ∘ f) → isSur g
∘-sur' f g compSur = λ y → ∃-elim trunc (λ a x → ∃-intro (f a) x) (compSur y)

-- 6. Докажите, что функция является биекцией тогда и только тогда, когда она является инъекцией и сюръекцией.

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij : {A B : Set} → (A → B) → Set
isBij {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

isBij-isInj : {A B : Set} (f : A → B) → isBij f → isInj f
isBij-isInj f (g , (inj , sur)) x y p =
  begin
    x
  ≡⟨ sym (inj x) ⟩
    g (f x)
  ≡⟨ cong (λ x → g x) p ⟩
    g (f y)
  ≡⟨ inj y ⟩
    y
  ∎

isBij-isSur : {A B : Set} (f : A → B) → isBij f → isSur f
isBij-isSur f (g , (inj , sur)) y = ∃-intro (g y) (sur y)

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

-- Эта лемма вам может пригодится
sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} (p : a ≡ a') → subst B p b ≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl q = cong (_,_ _) q

-- isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

isInj-isSur-isBij : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → isBij f
isInj-isSur-isBij {A} Bs f fi fs =
  (λ b → proj₁ (isInj-isSur-isBij' Bs f fi fs b)) ,
  proof' ,
  (λ b → proj₂ (isInj-isSur-isBij' Bs f fi fs b))
  where
    isInj-isSur-isBij' : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f →
      (y : B) → Σ[ x ∶ A ] (f x ≡ y)
    isInj-isSur-isBij' Bs f fi fs b with (fs b)
    isInj-isSur-isBij' {A} {B} Bs f fi fs b | v = ∃-elim Σ-isProp (λ x y → (x , y)) v
      where
        Σ-isProp : isProp (Σ[ x ∶ A ] (f x ≡ b))
        Σ-isProp (x1 , x2) (y1 , y2) = sigmaExt lem (Bs (f y1) b (subst (λ z → f z ≡ b) (fi x1 y1 (trans x2 (sym y2))) x2) y2)
          where
            lem : x1 ≡ y1
            lem = fi x1 y1 (trans x2 (sym y2))
            
    proof' : (x : A) → proj₁ (isInj-isSur-isBij' Bs f fi fs (f x)) ≡ x
    proof' x with (isInj-isSur-isBij' Bs f fi fs (f x))
    proof' x | (p1 , p2) = fi p1 x p2

-- 7. Докажите, что isBij является утверждением.

{-
isBij : {A B : Set} → (A → B) → Set
isBij {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)
-}

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

isBij-isProp : {A B : Set} → isSet A → isSet B → (f : A → B) → isProp (isBij f)
isBij-isProp {A} {B} sa sb f (g , (p1 , p2)) (h , (t1 , t2)) = sigmaExt (funExt g h proof) proof'
  where
    proof : (x : B) → g x ≡ h x
    proof x = begin
        g x
      ≡⟨ sym (t1 (g x)) ⟩
        h (f (g x))
      ≡⟨ cong (λ y → h y) (p2 x) ⟩
        h x
      ∎
    proof' : subst
      (λ g₁ → ((x : A) → g₁ (f x) ≡ x) × ((y : B) → f (g₁ y) ≡ y))
      (funExt g h proof) (p1 , p2)
      ≡ (t1 , t2)
    proof' = {!!}
-- 8. См. Cantor.agda.
