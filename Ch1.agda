{-# OPTIONS --without-K #-}

module Ch1 where

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Nat hiding (_+_; _*_)

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

-- todo: check this later

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
ℕ-rec-like c₀ c₁ n = iter c₀ (c₁ 0) n

-- todo: show def eqns 4 ℕ-rec hold propositionally

--( 5 )--------------------------------------------------------------

data ⊤₂ : Set where
  0₂ : ⊤₂
  1₂ : ⊤₂

⊤₂-rec : ∀ {i} {C : Set i} → C → C → ⊤₂ → C
⊤₂-rec c₀ c₁ 0₂ = c₀
⊤₂-rec c₀ c₁ 1₂ = c₁

_+_ : Set → Set → Set
A + B = Σ ⊤₂ (⊤₂-rec A B)

+-ind : ∀ {A B : Set}
          {C : A + B → Set}
      → ((a : A) → C (0₂ , a))
      → ((b : B) → C (1₂ , b))
      → (s : A + B) → C s

+-ind f g (0₂ , s) = f s
+-ind f g (1₂ , s) = g s

-- todo: 6, 7

--( 8 )--------------------------------------------------------------

Comm : ∀ {A : Set} → (A → A → A) → Set
Comm {A} _∘_ = ∀ {x y : A} →
  x ∘ y ≡ y ∘ x

Id : ∀ {A : Set} → (A → A → A) → A → Set
Id {A} _∘_ id = ∀ {x : A} →
  id ∘ x ≡ x ∘ id ×
  id ∘ x ≡ x

--/ identity includes commutativity at single point \--

meow : ∀ {i} {A : Set} {C : A → A → Set i}
     → (∀ {a b : A} → C a b)
     → (a : A) → (∀ {b : A} → C a b)
meow f a = f {a}

Id-via-Comm : ∀ {A : Set} → (A → A → A) → A → Set
Id-via-Comm {A} _∘_ id = ∀ {x : A} →
  meow (Comm _∘_) id {x} ×
  id ∘ x ≡ x

-------------------------------------------------------

Assoc : ∀ {A : Set} → (A → A → A) → Set
Assoc {A} _∘_ = ∀ {x y z : A} →
  (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)

L-Distr : ∀ {A : Set} → (A → A → A) → (A → A → A) → Set
L-Distr {A} _∘₁_ _∘₂_ = ∀ {x y z : A} →
  x ∘₁ (y ∘₂ z) ≡ (x ∘₁ y) ∘₂ (x ∘₁ z)

R-Distr : ∀ {A : Set} → (A → A → A) → (A → A → A) → Set
R-Distr {A} _∘₁_ _∘₂_ = ∀ {x y z : A} →
  (x ∘₁ y) ∘₂ z ≡ (x ∘₂ z) ∘₁ (y ∘₂ z)

Annihilates : ∀ {A : Set} → (A → A → A) → A → Set
Annihilates _∘_ z = ∀ {x} → x ∘ z ≡ z

-- maximum purist-structuralist style, just for educational purpose
-- in practice, this is usually done with records / parameterized modules

Magma : Set → Set
Magma C = (C → C → C) × C

Semiring : Set₁
Semiring = Σ structure rules
  where
    structure : Set₁
    structure = Σ Set (λ C → Magma C × Magma C)

    rules : structure → Set
    rules (C , (_∘₁_ , id₁) , (_∘₂_ , id₂))
      = Assoc _∘₁_
      × Id _∘₁_ id₁
      × Comm _∘₁_
      × Assoc _∘₂_
      × Id _∘₂_ id₂
      × L-Distr _∘₂_ _∘₁_
      × R-Distr _∘₁_ _∘₂_
      × Annihilates _∘₂_ id₁

add : ℕ → ℕ → ℕ
add x y = ℕ-rec x (λ _ x → suc x) y

_*_ : ℕ → ℕ → ℕ
x * y = ℕ-rec 0 (λ _ → add x) y

_^_ : ℕ → ℕ → ℕ
x ^ y = ℕ-rec 1 (λ _ → _*_ x) y

ℕ-semiring : Semiring
ℕ-semiring = (ℕ , (add , 0) , (_*_ , 1)) ,
  _ , _ , _ , _ , _ , _ , _ , _ -- not yet
