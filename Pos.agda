module Pos where

open import Data.Fin using (Fin; suc; inject₁; _<_)
open import Data.Fin.Patterns
open import Data.Fin.Properties using (<-trans; <-cmp)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Properties using (,-injective; ,-injectiveʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (Rel; StrictTotalOrder; IsStrictTotalOrder; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence; subst; sym; trans)

Pos : ℕ → ℕ → Set
Pos width height = Fin width × Fin height

_<ₚₒₛ_ : ∀ {width height : ℕ} → Rel (Pos width height) ℓ₀
⟨ x₁ , y₁ ⟩ <ₚₒₛ ⟨ x₂ , y₂ ⟩ = y₁ < y₂ ⊎ y₁ ≡ y₂ × x₁ < x₂

<ₚₒₛ-trans : ∀ {width height : ℕ} → Relation.Binary.Transitive (_<ₚₒₛ_ {width} {height})
<ₚₒₛ-trans (inj₁ y₁<y₂) (inj₁ y₂<y₃) = inj₁ (<-trans y₁<y₂ y₂<y₃)
<ₚₒₛ-trans (inj₁ y₁<y₂) (inj₂ ⟨ y₂≡y₃ , x₂<x₃ ⟩) = inj₁ (subst _ y₂≡y₃ y₁<y₂)
<ₚₒₛ-trans (inj₂ ⟨ y₁≡y₂ , x₁<x₂ ⟩) (inj₁ y₂<y₃) = inj₁ (subst _ (sym y₁≡y₂) y₂<y₃)
<ₚₒₛ-trans (inj₂ ⟨ y₁≡y₂ , x₁<x₂ ⟩) (inj₂ ⟨ y₂≡y₃ , x₂<x₃ ⟩) = inj₂ ⟨ trans y₁≡y₂ y₂≡y₃ , <-trans x₁<x₂ x₂<x₃ ⟩

<ₚₒₛ-cmp : ∀ {width height : ℕ} → Trichotomous _≡_ (_<ₚₒₛ_ {width} {height})
<ₚₒₛ-cmp ⟨ x₁ , y₁ ⟩ ⟨ x₂ , y₂ ⟩ with <-cmp y₁ y₂ | <-cmp x₁ x₂
... | tri< y₁<y₂ ¬y₁≡y₂ ¬y₂<y₁ | _ = tri<
                                       (inj₁ y₁<y₂)
                                       (λ ⟨x₁,y₁⟩≡⟨x₂,y₂⟩ → ¬y₁≡y₂ (,-injectiveʳ ⟨x₁,y₁⟩≡⟨x₂,y₂⟩))
                                       λ{(inj₁ y₂<y₁) → ¬y₂<y₁ y₂<y₁ ; (inj₂ ⟨ y₂≡y₁ , _ ⟩) → ¬y₁≡y₂ (sym y₂≡y₁)}
... | tri≈ ¬y₁<y₂ refl ¬y₂<y₁ | tri< x₁<x₂ ¬x₁≡x₂ ¬x₂<x₁ = tri<
                                                             (inj₂ ⟨ refl , x₁<x₂ ⟩)
                                                             (λ ⟨x₁,y₁⟩≡⟨x₂,y₁⟩ → ¬x₁≡x₂ (proj₁ (,-injective ⟨x₁,y₁⟩≡⟨x₂,y₁⟩)))
                                                             λ{(inj₁ y₂<y₁) → ¬y₂<y₁ y₂<y₁ ; (inj₂ ⟨ _ , x₂<x₁ ⟩) → ¬x₂<x₁ x₂<x₁}
... | tri≈ ¬y₁<y₂ refl ¬y₂<y₁ | tri≈ ¬x₁<x₂ refl ¬x₂<x₁ = tri≈
                                                            (λ{(inj₁ y₂<y₁) → ¬y₂<y₁ y₂<y₁ ; (inj₂ ⟨ _ , x₂<x₁ ⟩) → ¬x₂<x₁ x₂<x₁})
                                                            refl
                                                            λ{(inj₁ y₂<y₁) → ¬y₂<y₁ y₂<y₁ ; (inj₂ ⟨ _ , x₂<x₁ ⟩) → ¬x₂<x₁ x₂<x₁}
... | tri≈ ¬y₁<y₂ refl ¬y₂<y₁ | tri> ¬x₁<x₂ ¬x₁≡x₂ x₂<x₁ = tri>
                                                             (λ{(inj₁ y₂<y₁) → ¬y₂<y₁ y₂<y₁ ; (inj₂ ⟨ _ , x₁<x₂ ⟩) → ¬x₁<x₂ x₁<x₂})
                                                             (λ ⟨x₁,y₁⟩≡⟨x₂,y₁⟩ → ¬x₁≡x₂ (proj₁ (,-injective ⟨x₁,y₁⟩≡⟨x₂,y₁⟩)))
                                                             (inj₂ ⟨ refl , x₂<x₁ ⟩)
... | tri> ¬y₁<y₂ ¬y₁≡y₂ y₂<y₁ | _ = tri>
                                       (λ{(inj₁ y₁<y₂) → ¬y₁<y₂ y₁<y₂ ; (inj₂ ⟨ y₁≡y₂ , _ ⟩) → ¬y₁≡y₂ y₁≡y₂})
                                       (λ ⟨x₁,y₁⟩≡⟨x₂,y₂⟩ → ¬y₁≡y₂ (,-injectiveʳ ⟨x₁,y₁⟩≡⟨x₂,y₂⟩))
                                       (inj₁ y₂<y₁)


Pos-<-isStrictTotalOrder : ∀ {width height : ℕ} → IsStrictTotalOrder _≡_ (_<ₚₒₛ_ {width} {height})
Pos-<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <ₚₒₛ-trans
  ; compare       = <ₚₒₛ-cmp
  }

Pos-<-strictTotalOrder : ∀ {width height : ℕ} → StrictTotalOrder _ _ _
Pos-<-strictTotalOrder {width} {height} = record
  { isStrictTotalOrder = Pos-<-isStrictTotalOrder {width} {height}
  }


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
