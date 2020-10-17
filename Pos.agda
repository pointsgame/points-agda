module Pos where

open import Data.Fin using (Fin; suc; inject₁; _<_)
open import Data.Fin.Patterns
open import Data.Fin.Properties using (<-strictTotalOrder)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Function using (_$_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (StrictTotalOrder)

Pos : ℕ → ℕ → Set
Pos width height = Fin width × Fin height

Pos-strictTotalOrder : ∀ {width height : ℕ} → StrictTotalOrder _ _ _
Pos-strictTotalOrder {width} {height} = ×-strictTotalOrder (<-strictTotalOrder width) (<-strictTotalOrder height)

sucx : ∀ {width height : ℕ} → Pos width height → Pos (suc width) height
sucx ⟨ x , y ⟩ = ⟨ suc x , y ⟩

sucy : ∀ {width height : ℕ} → Pos width height → Pos width (suc height)
sucy ⟨ x , y ⟩ = ⟨ x , suc y ⟩

-- x does right, y goes down
data Adjacent : {width height : ℕ} → Pos width height → Pos width height → Set where
  adj→ : ∀ {width height : ℕ} → Adjacent {suc (suc width)} {suc height} (⟨ 0F , 0F ⟩) ⟨ 1F , 0F ⟩
  adj↓ : ∀ {width height : ℕ} → Adjacent {suc width} {suc (suc height)} (⟨ 0F , 0F ⟩) ⟨ 0F , 1F ⟩
  adj↳ : ∀ {width height : ℕ} → Adjacent {suc (suc width)} {suc (suc height)} (⟨ 0F , 0F ⟩) ⟨ 1F , 1F ⟩
  adj↱ : ∀ {width height : ℕ} → Adjacent {suc (suc width)} {suc (suc height)} (⟨ 0F , 1F ⟩) ⟨ 1F , 0F ⟩
  adj⇉ : ∀ {width height : ℕ} {pos₁ pos₂ : Pos width height} → Adjacent {width} {height} pos₁ pos₂ → Adjacent {suc width} {height} (sucx pos₁) (sucx pos₂)
  adj⇊ : ∀ {width height : ℕ} {pos₁ pos₂ : Pos width height} → Adjacent {width} {height} pos₁ pos₂ → Adjacent {width} {suc height} (sucy pos₁) (sucy pos₂)
  adj↔ : ∀ {width height : ℕ} {pos₁ pos₂ : Pos width height} → Adjacent {width} {height} pos₁ pos₂ → Adjacent {width} {height} pos₂ pos₁

adjacent-lemm₁ : ∀ {width height : ℕ} (x : Fin width) (y : Fin height) → Adjacent (⟨ suc x , y ⟩) ⟨ inject₁ x , y ⟩
adjacent-lemm₁ 0F 0F = adj↔ adj→
adjacent-lemm₁ (suc x) 0F = adj⇉ (adjacent-lemm₁ x 0F)
adjacent-lemm₁ x (suc y) = adj⇊ (adjacent-lemm₁ x y)

adjacent-lemm₂ : ∀ {width height : ℕ} (x : Fin width) (y : Fin height) → Adjacent (⟨ x , suc y ⟩) ⟨ x , inject₁ y ⟩
adjacent-lemm₂ 0F 0F = adj↔ adj↓
adjacent-lemm₂ 0F (suc y) = adj⇊ (adjacent-lemm₂ 0F y)
adjacent-lemm₂ (suc x) y = adj⇉ (adjacent-lemm₂ x y)

n : ∀ {width height : ℕ} → (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
n ⟨ _ , 0F ⟩ = nothing
n ⟨ x , suc y ⟩ = just ⟨ ⟨ x , inject₁ y ⟩ , adjacent-lemm₂ x y ⟩

s : ∀ {width height : ℕ} → (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
s {_} {1} ⟨ _ , 0F ⟩ = nothing
s {_} {suc (suc _)} ⟨ x , 0F ⟩ = just ⟨ ⟨ x , 1F ⟩ , adj↔ (adjacent-lemm₂ x 0F) ⟩
s ⟨ x , suc y ⟩ = Maybe.map (λ{⟨ ⟨ x₁ , y₁ ⟩ , adj ⟩ → ⟨ ⟨ x₁ , suc y₁ ⟩ , adj⇊ adj ⟩}) $ s ⟨ x , y ⟩

w : ∀ {width height : ℕ} → (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
w ⟨ 0F , _ ⟩ = nothing
w ⟨ suc x , y ⟩ = just ⟨ ⟨ inject₁ x , y ⟩ , adjacent-lemm₁ x y ⟩

e : ∀ {width height : ℕ} → (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
e {1} {_} ⟨ 0F , _ ⟩ = nothing
e {suc (suc _)} {_} ⟨ 0F , y ⟩ = just ⟨ ⟨ 1F , y ⟩ , adj↔ (adjacent-lemm₁ 0F y) ⟩
e ⟨ suc x , y ⟩ = Maybe.map (λ{⟨ ⟨ x₁ , y₁ ⟩ , adj ⟩ → ⟨ ⟨ suc x₁ , y₁ ⟩ , adj⇉ adj ⟩}) $ s ⟨ x , y ⟩
