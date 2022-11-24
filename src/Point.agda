{-# OPTIONS --safe #-}

module Point where

open import Data.Bool using (false; true)
open import Relation.Nullary using (Dec; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool
open import Player

data Point : Set where
  EmptyPoint : Point
  PlayerPoint : Player → Point
  BasePoint : Player → Bool → Point
  EmptyBasePoint : Player → Point

_≟ₚₜ_ : (point₁ point₂ : Point) → Dec (point₁ ≡ point₂)
EmptyPoint ≟ₚₜ EmptyPoint = true because ofʸ refl
EmptyPoint ≟ₚₜ PlayerPoint _ = false because ofⁿ (λ ())
EmptyPoint ≟ₚₜ BasePoint _ _ = false because ofⁿ (λ ())
EmptyPoint ≟ₚₜ EmptyBasePoint _ = false because ofⁿ (λ ())
PlayerPoint _ ≟ₚₜ EmptyPoint = false because ofⁿ (λ ())
PlayerPoint Red ≟ₚₜ PlayerPoint Red = true because ofʸ refl
PlayerPoint Red ≟ₚₜ PlayerPoint Black = false because ofⁿ (λ ())
PlayerPoint Black ≟ₚₜ PlayerPoint Red = false because ofⁿ (λ ())
PlayerPoint Black ≟ₚₜ PlayerPoint Black = true because ofʸ refl
PlayerPoint _ ≟ₚₜ BasePoint _ _ = false because ofⁿ (λ ())
PlayerPoint _ ≟ₚₜ EmptyBasePoint _ = false because ofⁿ (λ ())
BasePoint _ _ ≟ₚₜ EmptyPoint = false because ofⁿ (λ ())
BasePoint _ _ ≟ₚₜ PlayerPoint _ = false because ofⁿ (λ ())
BasePoint Red false ≟ₚₜ BasePoint Red false = true because ofʸ refl
BasePoint Red true ≟ₚₜ BasePoint Red true = true because ofʸ refl
BasePoint Black false ≟ₚₜ BasePoint Black false = true because ofʸ refl
BasePoint Black true ≟ₚₜ BasePoint Black true = true because ofʸ refl
BasePoint _ false ≟ₚₜ BasePoint _ true = false because ofⁿ (λ ())
BasePoint _ true ≟ₚₜ BasePoint _ false = false because ofⁿ (λ ())
BasePoint Red _ ≟ₚₜ BasePoint Black _ = false because ofⁿ (λ ())
BasePoint Black _ ≟ₚₜ BasePoint Red _ = false because ofⁿ (λ ())
BasePoint _ _ ≟ₚₜ EmptyBasePoint _ = false because ofⁿ (λ ())
EmptyBasePoint _ ≟ₚₜ EmptyPoint = false because ofⁿ (λ ())
EmptyBasePoint _ ≟ₚₜ PlayerPoint _ = false because ofⁿ (λ ())
EmptyBasePoint _ ≟ₚₜ BasePoint _ _ = false because ofⁿ (λ ())
EmptyBasePoint Red ≟ₚₜ EmptyBasePoint Red = true because ofʸ refl
EmptyBasePoint Red ≟ₚₜ EmptyBasePoint Black = false because ofⁿ (λ ())
EmptyBasePoint Black ≟ₚₜ EmptyBasePoint Red = false because ofⁿ (λ ())
EmptyBasePoint Black ≟ₚₜ EmptyBasePoint Black = true because ofʸ refl
