{-# OPTIONS --without-K #-}

module Ch1 where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat

--( 1 )--------------------------------------------------------------

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

∘-assoc : ∀ {A B C D} {f : C → D} {g : B → C} {h : A → B}
        → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
∘-assoc = refl

--( 2 )--------------------------------------------------------------

×-rec : ∀ {A B C : Set} → (A → B → C) → A × B → C
×-rec f p = f (proj₁ p) (proj₂ p)

Σ-rec : ∀ {A C : Set} {B : A → Set} → ((x : A) → B x → C) → Σ A B → C
Σ-rec f p = f (proj₁ p) (proj₂ p)

--( 3 )--------------------------------------------------------------

×-uniq : ∀ {A B : Set} {p : A × B} → (proj₁ p , proj₂ p) ≡ p
×-uniq = refl

×-ind : ∀ {A B : Set} {C : A × B → Set} → ((a : A) → (b : B) → C (a , b)) → (p : A × B) → C p
×-ind f p = f (proj₁ p) (proj₂ p)

Σ-uniq : ∀ {A : Set} {B : A → Set} {p : Σ A B} → (proj₁ p , proj₂ p) ≡ p
Σ-uniq = refl

Σ-ind : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
      → ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
Σ-ind f p = f (proj₁ p) (proj₂ p)

--( 4 )--------------------------------------------------------------

iter : ∀ {C : Set} → C → (C → C) → ℕ → C
iter c₀ cₛ      0  = c₀
iter c₀ cₛ (suc n) = cₛ (iter c₀ cₛ n)

ℕ-Rec : Set₁
ℕ-Rec = ∀ {C : Set} → C → (ℕ → C → C) → ℕ → C

ℕ-rec : ℕ-Rec
ℕ-rec c₀ cₛ      0  = c₀
ℕ-rec c₀ cₛ (suc n) = cₛ n (ℕ-rec c₀ cₛ n)

ℕ-rec-like : ℕ-Rec
ℕ-rec-like c₀ c₁ n = iter c₀ (c₁ 0) n -- ?
