{-# OPTIONS --safe #-}

module Pos where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; suc; inject₁; _<_; _≟_)
open import Data.Fin.Patterns
open import Data.Fin.Properties using (<-strictTotalOrder; *↔×)
open import Data.Maybe as Maybe using (Maybe; nothing; just; _>>=_)
open import Data.Nat using (ℕ; suc; _*_)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Function using (_$_; _∘_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; _≢_; ≢-sym)
open import Relation.Nullary using (¬_; Dec)

private
  variable
    width height : ℕ

-- x goes right, y goes down
Pos : ℕ → ℕ → Set
Pos width height = Fin width × Fin height

toFin : Pos width height → Fin (width * height)
toFin = Function.Inverse.from *↔×

_≟ₚₒₛ_ : (pos₁ pos₂ : Pos width height) → Dec (pos₁ ≡ pos₂)
_≟ₚₒₛ_ {width} {height} = ≡-dec (_≟_ {width}) (_≟_ {height})

infix 4 _≟ₚₒₛ_

Pos-strictTotalOrder : ∀ {width height : ℕ} → StrictTotalOrder ℓ₀ ℓ₀ ℓ₀
Pos-strictTotalOrder {width} {height} = ×-strictTotalOrder (<-strictTotalOrder width) (<-strictTotalOrder height)

Adjacent→ : Pos width height → Pos width height → Set
Adjacent→ (x₁ , y₁) (x₂ , y₂) = suc x₁ ≡ inject₁ x₂ × y₁ ≡ y₂

Adjacent↓ : Pos width height → Pos width height → Set
Adjacent↓ (x₁ , y₁) (x₂ , y₂) = x₁ ≡ x₂ × suc y₁ ≡ inject₁ y₂

Adjacent↘ : Pos width height → Pos width height → Set
Adjacent↘ (x₁ , y₁) (x₂ , y₂) = suc x₁ ≡ inject₁ x₂ × suc y₁ ≡ inject₁ y₂

Adjacent↗ : Pos width height → Pos width height → Set
Adjacent↗ (x₁ , y₁) (x₂ , y₂) = suc x₁ ≡ inject₁ x₂ × inject₁ y₁ ≡ suc y₂

Adjacent← : Pos width height → Pos width height → Set
Adjacent← pos₁ pos₂ = Adjacent→ pos₂ pos₁

Adjacent↑ : Pos width height → Pos width height → Set
Adjacent↑ pos₁ pos₂ = Adjacent↓ pos₂ pos₁

Adjacent↖ : Pos width height → Pos width height → Set
Adjacent↖ pos₁ pos₂ = Adjacent↘ pos₂ pos₁

Adjacent↙ : Pos width height → Pos width height → Set
Adjacent↙ pos₁ pos₂ = Adjacent↗ pos₂ pos₁

data Adjacent (pos₁ pos₂ : Pos width height) : Set where
  adj→ : Adjacent→ pos₁ pos₂ → Adjacent pos₁ pos₂
  adj← : Adjacent← pos₁ pos₂ → Adjacent pos₁ pos₂
  adj↓ : Adjacent↓ pos₁ pos₂ → Adjacent pos₁ pos₂
  adj↑ : Adjacent↑ pos₁ pos₂ → Adjacent pos₁ pos₂
  adj↘ : Adjacent↘ pos₁ pos₂ → Adjacent pos₁ pos₂
  adj↖ : Adjacent↖ pos₁ pos₂ → Adjacent pos₁ pos₂
  adj↗ : Adjacent↗ pos₁ pos₂ → Adjacent pos₁ pos₂
  adj↙ : Adjacent↙ pos₁ pos₂ → Adjacent pos₁ pos₂

adjacent-symm : ∀ {pos₁ pos₂ : Pos width height} → Adjacent pos₁ pos₂ → Adjacent pos₂ pos₁
adjacent-symm (adj→ adj) = adj← adj
adjacent-symm (adj← adj) = adj→ adj
adjacent-symm (adj↓ adj) = adj↑ adj
adjacent-symm (adj↑ adj) = adj↓ adj
adjacent-symm (adj↘ adj) = adj↖ adj
adjacent-symm (adj↖ adj) = adj↘ adj
adjacent-symm (adj↗ adj) = adj↙ adj
adjacent-symm (adj↙ adj) = adj↗ adj

adjacent→↓↘ : ∀ {pos₁ pos₂ pos₃ : Pos width height} → Adjacent→ pos₁ pos₂ → Adjacent↓ pos₂ pos₃ → Adjacent↘ pos₁ pos₃
adjacent→↓↘ adj₁ adj₂ rewrite sym $ proj₁ adj₂ | proj₂ adj₁ = (proj₁ adj₁ , proj₂ adj₂)

adjacent→↑↗ : ∀ {pos₁ pos₂ pos₃ : Pos width height} → Adjacent→ pos₁ pos₂ → Adjacent↓ pos₃ pos₂ → Adjacent↗ pos₁ pos₃
adjacent→↑↗ adj₁ adj₂ rewrite proj₁ adj₂ | proj₂ adj₁ = (proj₁ adj₁ , sym (proj₂ adj₂))

suc≢inject₁ : ∀ {n : ℕ} {x : Fin n} → suc x ≢ inject₁ x
suc≢inject₁ = ≢-sym $ <⇒≢ $ ≤̄⇒inject₁< ≤-refl where open Data.Fin.Properties

adjacent-⊥ : ∀ {pos : Pos width height} → ¬ Adjacent pos pos
adjacent-⊥ (adj→ (p , _)) = suc≢inject₁ p
adjacent-⊥ (adj← (p , _)) = suc≢inject₁ p
adjacent-⊥ (adj↓ (_ , p)) = suc≢inject₁ p
adjacent-⊥ (adj↑ (_ , p)) = suc≢inject₁ p
adjacent-⊥ (adj↘ (p , _)) = suc≢inject₁ p
adjacent-⊥ (adj↖ (p , _)) = suc≢inject₁ p
adjacent-⊥ (adj↗ (p , _)) = suc≢inject₁ p
adjacent-⊥ (adj↙ (p , _)) = suc≢inject₁ p

n : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↑ pos₁ pos₂)
n (_ , 0F) = nothing
n (x , suc y) = just ((x , inject₁ y) , (refl , refl))

s : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↓ pos₁ pos₂)
s {_} {1} (_ , 0F) = nothing
s {_} {suc (suc _)} (x , 0F) = just ((x , 1F) , (refl , refl))
s (x , suc y) = Maybe.map (λ{((x₁ , y₁) , adj) → ((x₁ , suc y₁) , (proj₁ adj , cong suc (proj₂ adj)))}) $ s (x , y)

w : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent← pos₁ pos₂)
w (0F , _) = nothing
w (suc x , y) = just ((inject₁ x , y) , (refl , refl))

e : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent→ pos₁ pos₂)
e {1} {_} (0F , _) = nothing
e {suc (suc _)} {_} (0F , y) = just ((1F , y) , (refl , refl))
e (suc x , y) = Maybe.map (λ{((x₁ , y₁) , adj) → ((suc x₁ , y₁) , (cong suc (proj₁ adj) , proj₂ adj))}) $ e (x , y)

nw : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↖ pos₁ pos₂)
nw pos = do (npos , adj₁) ← n pos
            (nwpos , adj₂) ← w npos
            just (nwpos , adjacent→↓↘ adj₂ adj₁)

ne : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↗ pos₁ pos₂)
ne pos = do (epos , adj₁) ← e pos
            (nepos , adj₂) ← n epos
            just (nepos , adjacent→↑↗ adj₁ adj₂)

sw : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↙ pos₁ pos₂)
sw pos = do (spos , adj₁) ← s pos
            (swpos , adj₂) ← w spos
            just (swpos , adjacent→↑↗ adj₂ adj₁)

se : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↘ pos₁ pos₂)
se pos = do (epos , adj₁) ← e pos
            (sepos , adj₂) ← s epos
            just (sepos , adjacent→↓↘ adj₁ adj₂)

n‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
n‵ = Maybe.map (Data.Product.map₂ adj↑) ∘ n

s‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
s‵ = Maybe.map (Data.Product.map₂ adj↓) ∘ s

w‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
w‵ = Maybe.map (Data.Product.map₂ adj←) ∘ w

e‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
e‵ = Maybe.map (Data.Product.map₂ adj→) ∘ e

nw‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
nw‵ = Maybe.map (Data.Product.map₂ adj↖) ∘ nw

ne‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
ne‵ = Maybe.map (Data.Product.map₂ adj↗) ∘ ne

sw‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
sw‵ = Maybe.map (Data.Product.map₂ adj↙) ∘ sw

se‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
se‵ = Maybe.map (Data.Product.map₂ adj↘) ∘ se

data Direction : Set where
  dir→ : Direction
  dir↘ : Direction
  dir↓ : Direction
  dir↙ : Direction
  dir← : Direction
  dir↖ : Direction
  dir↑ : Direction
  dir↗ : Direction

inverse : Direction → Direction
inverse dir→ = dir←
inverse dir↘ = dir↖
inverse dir↓ = dir↑
inverse dir↙ = dir↗
inverse dir← = dir→
inverse dir↖ = dir↘
inverse dir↑ = dir↓
inverse dir↗ = dir↙

rotate : Direction → Direction
rotate dir→ = dir↘
rotate dir↘ = dir↓
rotate dir↓ = dir↙
rotate dir↙ = dir←
rotate dir← = dir↖
rotate dir↖ = dir↑
rotate dir↑ = dir↗
rotate dir↗ = dir→

rotate¬adjacent : Direction → Direction
rotate¬adjacent dir→ = dir↙
rotate¬adjacent dir↘ = dir↙
rotate¬adjacent dir↓ = dir↖
rotate¬adjacent dir↙ = dir↖
rotate¬adjacent dir← = dir↗
rotate¬adjacent dir↖ = dir↗
rotate¬adjacent dir↑ = dir↘
rotate¬adjacent dir↗ = dir↘

direction : ∀ {pos₁ pos₂ : Pos width height} → Adjacent pos₁ pos₂ → Direction
direction (adj→ _) = dir→
direction (adj← _) = dir←
direction (adj↓ _) = dir↓
direction (adj↑ _) = dir↑
direction (adj↘ _) = dir↘
direction (adj↖ _) = dir↖
direction (adj↗ _) = dir↗
direction (adj↙ _) = dir↙

direction→pos : Direction → (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
direction→pos dir→ = e‵
direction→pos dir↘ = se‵
direction→pos dir↓ = s‵
direction→pos dir↙ = sw‵
direction→pos dir← = w‵
direction→pos dir↖ = nw‵
direction→pos dir↑ = n‵
direction→pos dir↗ = ne‵
