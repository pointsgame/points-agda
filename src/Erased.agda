{-# OPTIONS --safe --erasure #-}

open import Data.Empty using (⊥)
open import Level using (Level; _⊔_)
open import Function using (id)

⊥-recover : @0 ⊥ → ⊥
⊥-recover ()

private
  variable
    a b c p q : Level
    A : Set a
    B : Set b
    C : Set c

-- Like Σ from Data.Product but with erased proj₂
record Σₑ (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,ₑ_
  field
    proj₁ₑ : A
    @0 proj₂ₑ : B proj₁ₑ

open Σₑ public

infixr 4 _,ₑ_

infix 2 Σₑ-syntax

Σₑ-syntax : (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σₑ-syntax = Σₑ

syntax Σₑ-syntax A (λ x → B) = Σₑ[ x ∈ A ] B

infix 2 ∃ₑ-syntax

∃ₑ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ₑ = Σₑ _

∃ₑ-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ₑ-syntax = ∃ₑ

syntax ∃ₑ-syntax (λ x → B) = ∃ₑ[ x ] B

_×ₑ_ : (A : Set a) (B : Set b) → Set (a ⊔ b)
A ×ₑ B = Σₑ[ x ∈ A ] B

mapₑ : ∀ {P : A → Set p} {Q : B → Set q} →
       (f : A → B) → @0 (∀ {x} → P x → Q (f x)) →
       Σₑ A P → Σₑ B Q
mapₑ f g (x ,ₑ y) = (f x ,ₑ g y)

map₁ₑ : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → (A → B) → A ×ₑ C → B ×ₑ C
map₁ₑ f = mapₑ f id

map₂ₑ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} →
        @0 (∀ {x} → B x → C x) → Σₑ A B → Σₑ A C
map₂ₑ f = mapₑ id f
