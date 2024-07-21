{-# OPTIONS --safe #-}

module Pos where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; suc; inject₁; _<_; _≟_)
open import Data.Fin.Patterns
open import Data.Fin.Properties using (<-strictTotalOrder)
open import Data.Maybe as Maybe using (Maybe; nothing; just; _>>=_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Function using (_$_; _∘_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (¬_; Dec)

private
  variable
    width height : ℕ

Pos : ℕ → ℕ → Set
Pos width height = Fin width × Fin height

_≟ₚₒₛ_ : (pos₁ pos₂ : Pos width height) → Dec (pos₁ ≡ pos₂)
_≟ₚₒₛ_ {width} {height} = ≡-dec (_≟_ {width}) (_≟_ {height})

infix 4 _≟ₚₒₛ_

Pos-strictTotalOrder : ∀ {width height : ℕ} → StrictTotalOrder ℓ₀ ℓ₀ ℓ₀
Pos-strictTotalOrder {width} {height} = ×-strictTotalOrder (<-strictTotalOrder width) (<-strictTotalOrder height)

sucx : Pos width height → Pos (suc width) height
sucx (x , y) = suc x , y

sucy : Pos width height → Pos width (suc height)
sucy (x , y) = x , suc y

data Adjacent→ : Pos width height → Pos width height → Set where
  adj→ : Adjacent→ {suc (suc width)} {suc height} (0F , 0F) (1F , 0F)
  adj⇉ : {pos₁ pos₂ : Pos width height} → Adjacent→ {width} {height} pos₁ pos₂ → Adjacent→ {suc width} {height} (sucx pos₁) (sucx pos₂)
  adj⇊ : {pos₁ pos₂ : Pos width height} → Adjacent→ {width} {height} pos₁ pos₂ → Adjacent→ {width} {suc height} (sucy pos₁) (sucy pos₂)

data Adjacent↓ : Pos width height → Pos width height → Set where
  adj↓ : Adjacent↓ {suc width} {suc (suc height)} (0F , 0F) (0F , 1F)
  adj⇉ : {pos₁ pos₂ : Pos width height} → Adjacent↓ {width} {height} pos₁ pos₂ → Adjacent↓ {suc width} {height} (sucx pos₁) (sucx pos₂)
  adj⇊ : {pos₁ pos₂ : Pos width height} → Adjacent↓ {width} {height} pos₁ pos₂ → Adjacent↓ {width} {suc height} (sucy pos₁) (sucy pos₂)

data Adjacent↘ : Pos width height → Pos width height → Set where
  adj↘ : Adjacent↘ {suc (suc width)} {suc (suc height)} (0F , 0F) (1F , 1F)
  adj⇉ : {pos₁ pos₂ : Pos width height} → Adjacent↘ {width} {height} pos₁ pos₂ → Adjacent↘ {suc width} {height} (sucx pos₁) (sucx pos₂)
  adj⇊ : {pos₁ pos₂ : Pos width height} → Adjacent↘ {width} {height} pos₁ pos₂ → Adjacent↘ {width} {suc height} (sucy pos₁) (sucy pos₂)

data Adjacent↗ : Pos width height → Pos width height → Set where
  adj↗ : Adjacent↗ {suc (suc width)} {suc (suc height)} (0F , 1F) (1F , 0F)
  adj⇉ : {pos₁ pos₂ : Pos width height} → Adjacent↗ {width} {height} pos₁ pos₂ → Adjacent↗ {suc width} {height} (sucx pos₁) (sucx pos₂)
  adj⇊ : {pos₁ pos₂ : Pos width height} → Adjacent↗ {width} {height} pos₁ pos₂ → Adjacent↗ {width} {suc height} (sucy pos₁) (sucy pos₂)

Adjacent← : Pos width height → Pos width height → Set
Adjacent← pos₁ pos₂ = Adjacent→ pos₂ pos₁

Adjacent↑ : Pos width height → Pos width height → Set
Adjacent↑ pos₁ pos₂ = Adjacent↓ pos₂ pos₁

Adjacent↖ : Pos width height → Pos width height → Set
Adjacent↖ pos₁ pos₂ = Adjacent↘ pos₂ pos₁

Adjacent↙ : Pos width height → Pos width height → Set
Adjacent↙ pos₁ pos₂ = Adjacent↗ pos₂ pos₁

-- x goes right, y goes down
data Adjacent : Pos width height → Pos width height → Set where
  adj→ : Adjacent {suc (suc width)} {suc height} (0F , 0F) (1F , 0F)
  adj↓ : Adjacent {suc width} {suc (suc height)} (0F , 0F) (0F , 1F)
  adj↘ : Adjacent {suc (suc width)} {suc (suc height)} (0F , 0F) (1F , 1F)
  adj↗ : Adjacent {suc (suc width)} {suc (suc height)} (0F , 1F) (1F , 0F)
  adj⇉ : {pos₁ pos₂ : Pos width height} → Adjacent {width} {height} pos₁ pos₂ → Adjacent {suc width} {height} (sucx pos₁) (sucx pos₂)
  adj⇊ : {pos₁ pos₂ : Pos width height} → Adjacent {width} {height} pos₁ pos₂ → Adjacent {width} {suc height} (sucy pos₁) (sucy pos₂)
  adj↔ : {pos₁ pos₂ : Pos width height} → Adjacent {width} {height} pos₁ pos₂ → Adjacent {width} {height} pos₂ pos₁

adjacent→ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent→ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent→ adj→ = adj→
adjacent→ (adj⇉ adj) = adj⇉ (adjacent→ adj)
adjacent→ (adj⇊ adj) = adj⇊ (adjacent→ adj)

adjacent↓ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent↓ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent↓ adj↓ = adj↓
adjacent↓ (adj⇉ adj) = adj⇉ (adjacent↓ adj)
adjacent↓ (adj⇊ adj) = adj⇊ (adjacent↓ adj)

adjacent↘ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent↘ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent↘ adj↘ = adj↘
adjacent↘ (adj⇉ adj) = adj⇉ (adjacent↘ adj)
adjacent↘ (adj⇊ adj) = adj⇊ (adjacent↘ adj)

adjacent↗ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent↗ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent↗ adj↗ = adj↗
adjacent↗ (adj⇉ adj) = adj⇉ (adjacent↗ adj)
adjacent↗ (adj⇊ adj) = adj⇊ (adjacent↗ adj)

adjacent← : ∀ {pos₁ pos₂ : Pos width height} → Adjacent← pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent← = adj↔ ∘ adjacent→

adjacent↑ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent↑ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent↑ = adj↔ ∘ adjacent↓

adjacent↖ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent↖ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent↖ = adj↔ ∘ adjacent↘

adjacent↙ : ∀ {pos₁ pos₂ : Pos width height} → Adjacent↙ pos₁ pos₂ → Adjacent pos₁ pos₂
adjacent↙ = adj↔ ∘ adjacent↗


adjacent-⊥ : ∀ {pos : Pos width height} → ¬ Adjacent pos pos
adjacent-⊥ (adj⇉ adj) = adjacent-⊥ adj
adjacent-⊥ (adj⇊ adj) = adjacent-⊥ adj
adjacent-⊥ (adj↔ adj) = adjacent-⊥ adj

adjacent-lemm₁ : (x : Fin width) (y : Fin height) → Adjacent→ (inject₁ x , y) (suc x , y)
adjacent-lemm₁ 0F 0F = adj→
adjacent-lemm₁ 0F (suc y) = adj⇊ (adjacent-lemm₁ 0F y)
adjacent-lemm₁ (suc x) _ = adj⇉ (adjacent-lemm₁ x _)

adjacent-lemm₂ : (x : Fin width) (y : Fin height) → Adjacent↓ (x , inject₁ y) (x , suc y)
adjacent-lemm₂ 0F 0F = adj↓
adjacent-lemm₂ (suc x) 0F = adj⇉ (adjacent-lemm₂ x 0F)
adjacent-lemm₂ _ (suc y) = adj⇊ (adjacent-lemm₂ _ y)

adjacent-lemm₃ : (x : Fin width) (y : Fin height) → Adjacent↘ (inject₁ x , inject₁ y) (suc x , suc y)
adjacent-lemm₃ 0F 0F = adj↘
adjacent-lemm₃ 0F (suc y) = adj⇊ (adjacent-lemm₃ 0F y)
adjacent-lemm₃ (suc x) y = adj⇉ (adjacent-lemm₃ x y)

adjacent-lemm₄ : (x : Fin width) (y : Fin height) → Adjacent↗ (inject₁ x , suc y) (suc x , inject₁ y)
adjacent-lemm₄ 0F 0F = adj↗
adjacent-lemm₄ 0F (suc y) = adj⇊ (adjacent-lemm₄ 0F y)
adjacent-lemm₄ (suc x) y = adj⇉ (adjacent-lemm₄ x y)

¬adjacent↓₀ : ∀ {x₁ x₂ : Fin width} {y : Fin (suc height)} → ¬ Adjacent↓ (x₁ , y) (x₂ , 0F)
¬adjacent↓₀ (adj⇉ adj) = ¬adjacent↓₀ adj

¬adjacent↓₁ : ∀ {x₁ x₂ : Fin width} {y : Fin (suc height)} → ¬ Adjacent↓ (x₁ , suc y) (x₂ , 1F)
¬adjacent↓₁ (adj⇉ adj) = ¬adjacent↓₁ adj
¬adjacent↓₁ (adj⇊ adj) = ¬adjacent↓₀ adj

¬adjacent→₀ : ∀ {x : Fin (suc width)} {y₁ y₂ : Fin height} → ¬ Adjacent→ (x , y₁) (0F , y₂)
¬adjacent→₀ (adj⇊ adj) = ¬adjacent→₀ adj

adjacent→-refl₁ : ∀ {x₁ x₂ : Fin width} {y₁ y₂ : Fin height} → Adjacent→ (x₁ , y₁) (x₂ , y₂) → y₁ ≡ y₂
adjacent→-refl₁ adj→ = refl
adjacent→-refl₁ (adj⇉ adj) = adjacent→-refl₁ adj
adjacent→-refl₁ (adj⇊ adj→) = refl
adjacent→-refl₁ (adj⇊ (adj⇉ adj)) rewrite adjacent→-refl₁ (adj⇊ adj) = refl
adjacent→-refl₁ (adj⇊ (adj⇊ adj)) = cong suc (adjacent→-refl₁ (adj⇊ adj))

adjacent→-refl₂ : ∀ {x₁ : Fin (suc width)} {x₂ : Fin width} {y₁ y₂ : Fin height} → Adjacent→ (x₁ , y₁) (suc x₂ , y₂) → x₁ ≡ inject₁ x₂
adjacent→-refl₂ adj→ = refl
adjacent→-refl₂ {x₂ = 0F} (adj⇉ adj) = ⊥-elim (¬adjacent→₀ adj)
adjacent→-refl₂ {x₂ = suc _} (adj⇉ adj) = cong suc (adjacent→-refl₂ adj)
adjacent→-refl₂ (adj⇊ adj) = adjacent→-refl₂ adj

adjacent↓-refl₁ : ∀ {x₁ x₂ : Fin width} {y₁ y₂ : Fin height} → Adjacent↓ (x₁ , y₁) (x₂ , y₂) → x₁ ≡ x₂
adjacent↓-refl₁ adj↓ = refl
adjacent↓-refl₁ (adj⇉ adj↓) = refl
adjacent↓-refl₁ (adj⇉ (adj⇉ adj)) = cong suc (adjacent↓-refl₁ (adj⇉ adj))
adjacent↓-refl₁ (adj⇉ (adj⇊ adj)) rewrite adjacent↓-refl₁ (adj⇉ adj) = refl
adjacent↓-refl₁ (adj⇊ adj) = adjacent↓-refl₁ adj

adjacent↓-refl₂ : ∀ {x₁ x₂ : Fin width} {y₁ : Fin (suc height)} {y₂ : Fin height} → Adjacent↓ (x₁ , y₁) (x₂ , suc y₂) → y₁ ≡ inject₁ y₂
adjacent↓-refl₂ adj↓ = refl
adjacent↓-refl₂ (adj⇉ adj) = adjacent↓-refl₂ adj
adjacent↓-refl₂ {y₂ = 0F} (adj⇊ adj) = ⊥-elim (¬adjacent↓₀ adj)
adjacent↓-refl₂ {y₂ = suc y₂} (adj⇊ adj) = cong suc (adjacent↓-refl₂ adj)

adjacent→-dec : ∀ {x₁ x₂ : Fin width} {y₁ y₂ : Fin height} → Adjacent→ (x₁ , suc y₁) (x₂ , suc y₂) → Adjacent→ (x₁ , y₁) (x₂ , y₂)
adjacent→-dec (adj⇉ adj) = adj⇉ (adjacent→-dec adj)
adjacent→-dec {y₁ = 0F} {y₂ = 0F} (adj⇊ adj→) = adj→
adjacent→-dec {y₁ = 0F} (adj⇊ adj) = adj
adjacent→-dec {y₁ = suc _} (adj⇊ adj) = adj

adjacent↓-dec : ∀ {x₁ x₂ : Fin width} {y₁ y₂ : Fin height} → Adjacent↓ (suc x₁ , y₁) (suc x₂ , y₂) → Adjacent↓ (x₁ , y₁) (x₂ , y₂)
adjacent↓-dec (adj⇊ adj) = adj⇊ (adjacent↓-dec adj)
adjacent↓-dec {x₁ = 0F} {x₂ = 0F} (adj⇉ adj↓) = adj↓
adjacent↓-dec {x₁ = 0F} (adj⇉ adj) = adj
adjacent↓-dec {x₁ = suc _} (adj⇉ adj) = adj

adjacent→↓↘ : ∀ {pos₁ pos₂ pos₃ : Pos width height} → Adjacent→ pos₁ pos₂ → Adjacent↓ pos₂ pos₃ → Adjacent↘ pos₁ pos₃
adjacent→↓↘ adj→ (adj⇉ adj↓) = adj↘
adjacent→↓↘ (adj⇉ adj₁) (adj⇉ adj₂) = adj⇉ (adjacent→↓↘ adj₁ adj₂)
adjacent→↓↘ (adj⇉ adj₁) (adj⇊ adj₂) with adj₁ | adj₂
... | adj₁‵ | adj₂‵ rewrite adjacent→-refl₁ adj₁ | sym (adjacent↓-refl₁ adj₂) = adj⇉ (adj⇊ (adjacent→↓↘ (adjacent→-dec adj₁‵) (adjacent↓-dec adj₂‵)))
adjacent→↓↘ {pos₃ = (suc x₃ , 0F)} (adj⇊ adj₁) (adj⇉ adj₂) = ⊥-elim (¬adjacent↓₀ adj₂)
adjacent→↓↘ {pos₃ = (suc x₃ , 1F)} (adj⇊ adj₁) (adj⇉ adj₂) = ⊥-elim (¬adjacent↓₁ adj₂)
adjacent→↓↘ {pos₃ = (suc x₃ , suc (suc y₃))} (adj⇊ adj₁) (adj⇉ adj₂) rewrite sym (adjacent↓-refl₁ adj₂)
                                                                           | sym (adjacent→-refl₁ adj₁)
                                                                           | adjacent→-refl₂ adj₁
                                                                           | adjacent↓-refl₂ adj₂ = adj⇊ (adjacent-lemm₃ _ _)
adjacent→↓↘ (adj⇊ adj₁) (adj⇊ adj₂) = adj⇊ (adjacent→↓↘ adj₁ adj₂)

adjacent→↑↗ : ∀ {pos₁ pos₂ pos₃ : Pos width height} → Adjacent→ pos₁ pos₂ → Adjacent↓ pos₃ pos₂ → Adjacent↗ pos₁ pos₃
adjacent→↑↗ adj→ (adj⇉ ())
adjacent→↑↗ (adj⇉ adj₁) (adj⇉ adj₂) = adj⇉ (adjacent→↑↗ adj₁ adj₂)
adjacent→↑↗ {pos₁ = (suc _ , 0F)} {pos₃ = (_ , suc _)} (adj⇉ adj₁) (adj⇊ adj₂) with adjacent→-refl₁ adj₁
... | ()
adjacent→↑↗ {pos₁ = (suc _ , suc _)} {pos₃ = (0F , suc _)} (adj⇉ adj₁) (adj⇊ adj₂) with adjacent↓-refl₁ adj₂
... | ()
adjacent→↑↗ {pos₁ = (suc _ , suc _)} {pos₃ = (suc _ , suc _)} (adj⇉ adj₁) (adj⇊ adj₂) = adj⇊ (adj⇉ (adjacent→↑↗ (adjacent→-dec adj₁) (adjacent↓-dec adj₂)))
adjacent→↑↗ {pos₁ = (_ , suc _)} {pos₃ = (suc _ , _)} (adj⇊ adj₁) (adj⇉ adj₂) rewrite sym (adjacent↓-refl₁ adj₂)
                                                                                    | sym (adjacent→-refl₁ adj₁)
                                                                                    | adjacent→-refl₂ adj₁
                                                                                    | adjacent↓-refl₂ adj₂ = adjacent-lemm₄ _ _
adjacent→↑↗ (adj⇊ adj₁) (adj⇊ adj₂) = adj⇊ (adjacent→↑↗ adj₁ adj₂)

n : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↑ pos₁ pos₂)
n (_ , 0F) = nothing
n (x , suc y) = just ((x , inject₁ y) , adjacent-lemm₂ x y)

s : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent↓ pos₁ pos₂)
s {_} {1} (_ , 0F) = nothing
s {_} {suc (suc _)} (x , 0F) = just ((x , 1F) , adjacent-lemm₂ x 0F)
s (x , suc y) = Maybe.map (λ{((x₁ , y₁) , adj) → ((x₁ , suc y₁) , adj⇊ adj)}) $ s (x , y)

w : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent← pos₁ pos₂)
w (0F , _) = nothing
w (suc x , y) = just ((inject₁ x , y) , adjacent-lemm₁ x y)

e : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent→ pos₁ pos₂)
e {1} {_} (0F , _) = nothing
e {suc (suc _)} {_} (0F , y) = just ((1F , y) , adjacent-lemm₁ 0F y)
e (suc x , y) = Maybe.map (λ{((x₁ , y₁) , adj) → ((suc x₁ , y₁) , adj⇉ adj)}) $ e (x , y)

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
n‵ = Maybe.map (Data.Product.map₂ adjacent↑) ∘ n

s‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
s‵ = Maybe.map (Data.Product.map₂ adjacent↓) ∘ s

w‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
w‵ = Maybe.map (Data.Product.map₂ adjacent←) ∘ w

e‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
e‵ = Maybe.map (Data.Product.map₂ adjacent→) ∘ e

nw‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
nw‵ = Maybe.map (Data.Product.map₂ adjacent↖) ∘ nw

ne‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
ne‵ = Maybe.map (Data.Product.map₂ adjacent↗) ∘ ne

sw‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
sw‵ = Maybe.map (Data.Product.map₂ adjacent↙) ∘ sw

se‵ : (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
se‵ = Maybe.map (Data.Product.map₂ adjacent↘) ∘ se

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
direction adj→ = dir→
direction adj↓ = dir↓
direction adj↘ = dir↘
direction adj↗ = dir↗
direction (adj⇉ adj) = direction adj
direction (adj⇊ adj) = direction adj
direction (adj↔ adj) = inverse (direction adj)

direction→pos : Direction → (pos₁ : Pos width height) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)
direction→pos dir→ = e‵
direction→pos dir↘ = se‵
direction→pos dir↓ = s‵
direction→pos dir↙ = sw‵
direction→pos dir← = w‵
direction→pos dir↖ = nw‵
direction→pos dir↑ = n‵
direction→pos dir↗ = ne‵
