{-# OPTIONS --safe #-}

module Player where

open import Data.Bool using (false; true)
open import Relation.Nullary using (Dec; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Player : Set where
  Red : Player
  Black : Player

_≟ₚₗ_ : (player₁ player₂ : Player) → Dec (player₁ ≡ player₂)
Red ≟ₚₗ Red = true because ofʸ refl
Red ≟ₚₗ Black = false because ofⁿ (λ ())
Black ≟ₚₗ Red = false because ofⁿ (λ ())
Black ≟ₚₗ Black = true because ofʸ refl

next : Player → Player
next Red = Black
next Black = Red
