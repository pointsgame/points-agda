open import Data.Nat as Nat using (ℕ)

module Field {width height : ℕ} where

open import Data.Bool as Bool using (Bool; true; false; if_then_else_; not; _∨_)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Integer using (ℤ; 0ℤ; _+_; _-_; _*_; +_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Linked using (Linked; [-]) renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; proj₁; proj₂; map₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _∘_; case_of_)
open import Generic.Main using (_==_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (_because_; ofʸ)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Player
open import Point
open import Pos renaming (Pos to FinPos)

Pos : Set
Pos = FinPos width height

open import Data.Tree.AVL.Sets (Pos-strictTotalOrder {width} {height}) as S renaming (⟨Set⟩ to ⟨Set⟩ₚₒₛ)

record Field : Set where
  field
    scoreRed scoreBlack : ℕ
    moves : List (Pos × Player)
    lastSurroundChain : Maybe (List Pos × Player)
    points : Pos → Point

isPuttingAllowed : Field → Pos → Bool
isPuttingAllowed record { points = points } pos with points pos
... | EmptyPoint = true
... | EmptyBasePoint _ = true
... | _ = false

isPlayer : Field → Pos → Player → Bool
isPlayer record { points = points } pos player with points pos
... | PlayerPoint p = p == player
... | BasePoint p _ = p == player
... | _ = false

isPlayersPoint : Field → Pos → Player → Bool
isPlayersPoint record { points = points } pos player = points pos == PlayerPoint player

emptyField : Field
emptyField = record { scoreRed = 0
                    ; scoreBlack = 0
                    ; moves = []
                    ; lastSurroundChain = nothing
                    ; points = λ _ → EmptyPoint
                    }

{-# NON_TERMINATING #-}
wave : Pos → (Pos → Bool) → ⟨Set⟩ₚₒₛ
wave startPos f = wave' S.empty (S.singleton startPos)
  where nullₛ : ⟨Set⟩ₚₒₛ → Bool
        nullₛ s = List.null (S.toList s)
        unionₛ : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        unionₛ set₁ set₂ = List.foldl (Function.flip S.insert) set₁ (S.toList set₂)
        _\\ₛ_ : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        _\\ₛ_ set₁ set₂ = List.foldl (Function.flip S.delete) set₁ (S.toList set₂)
        neighborhood : Pos → List Pos
        neighborhood pos = List.mapMaybe (Maybe.map proj₁) $ n‵ pos
                                                           ∷ s‵ pos
                                                           ∷ w‵ pos
                                                           ∷ e‵ pos
                                                           ∷ []
        nextFront : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        nextFront passed front = (S.fromList $ List.boolFilter f $ List.concatMap neighborhood (S.toList front)) \\ₛ passed
        wave' : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        wave' passed front = if nullₛ front
                             then passed
                             else wave' (unionₛ passed front) (nextFront passed front)

getFirstNextPos : {centerPos pos : Pos} → Adjacent centerPos pos → Maybe (∃[ nextPos ] Adjacent centerPos nextPos)
getFirstNextPos adj = nothing

getNextPos : {centerPos pos : Pos} → Adjacent centerPos pos → Maybe (∃[ nextPos ] Adjacent centerPos nextPos)
getNextPos adj = direction→pos (rotate (direction adj)) _

getInputPoints : Field → (pos : Pos) → Player → List (∃[ chainPos ] Adjacent pos chainPos × ∃[ capturedPos ] Adjacent pos capturedPos)
getInputPoints fld pos player =
  let isDirectionPlayer : ((pos₁ : Pos) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)) → Bool
      isDirectionPlayer dir = Maybe.maybe′ (λ{⟨ dirPos , _ ⟩ → isPlayer fld dirPos player}) false $ dir pos
      list₁ = if not $ isDirectionPlayer w‵ then
                if isDirectionPlayer sw‵ then List.fromMaybe (Maybe.zip (sw‵ pos) (w‵ pos))
                else if isDirectionPlayer s‵ then List.fromMaybe (Maybe.zip (s‵ pos) (w‵ pos))
                else []
              else
                []
      list₂ = if not $ isDirectionPlayer n‵ then
                if isDirectionPlayer nw‵ then List.fromMaybe (Maybe.zip (nw‵ pos) (n‵ pos)) ++ list₁
                else if isDirectionPlayer w‵ then List.fromMaybe (Maybe.zip (w‵ pos) (n‵ pos)) ++ list₁
                else list₁
              else
                list₁
      list₃ = if not $ isDirectionPlayer e‵ then
                if isDirectionPlayer ne‵ then List.fromMaybe (Maybe.zip (ne‵ pos) (e‵ pos)) ++ list₂
                else if isDirectionPlayer n‵ then List.fromMaybe (Maybe.zip (n‵ pos) (e‵ pos)) ++ list₂
                else list₂
              else
                list₂
      list₄ = if not $ isDirectionPlayer s‵ then
                if isDirectionPlayer se‵ then List.fromMaybe (Maybe.zip (se‵ pos) (s‵ pos)) ++ list₃
                else if isDirectionPlayer e‵ then List.fromMaybe (Maybe.zip (e‵ pos) (s‵ pos)) ++ list₃
                else list₃
              else
                list₃
  in list₄

square : List Pos → ℤ
square [] = 0ℤ
square (pos ∷ tail) = square‵ $ pos ∷ tail
  where fiberBundle : Pos → Pos → ℤ
        fiberBundle ⟨ x₁ , y₁ ⟩ ⟨ x₂ , y₂ ⟩ = + toℕ x₁ * + toℕ y₂ - + toℕ y₁ * + toℕ x₂
        square‵ : List Pos → ℤ
        square‵ [] = 0ℤ
        square‵ (pos₁ ∷ []) = fiberBundle pos₁ pos
        square‵ (pos₁ ∷ pos₂ ∷ tail) = fiberBundle pos₁ pos₂ + square‵ (pos₂ ∷ tail)

open import Data.List.NonEmpty as NEL using (List⁺; _∷⁺_; head) renaming (_∷_ to _⁺∷_)

IsChain : List Pos → Set
IsChain = Linked Adjacent

IsChain⁺ : List⁺ Pos → Set
IsChain⁺ = IsChain ∘ NEL.toList

data IsRing : List Pos → Set where
  ring-init : ∀ {pos₁ pos₂ : Pos} → Adjacent pos₁ pos₂ → IsRing (pos₁ ∷ pos₂ ∷ [])
  ring-extend : ∀ {pos₁ pos₂ : Pos} {list : List Pos} → IsRing (pos₁ ∷ list) → IsRing (pos₁ ∷ pos₂ ∷ list)

IsRing⁺ : List⁺ Pos → Set
IsRing⁺ = IsRing ∘ NEL.toList

SameHead : {A : Set} → List⁺ A → List⁺ A → Set
SameHead a b = head a ≡ head b

data SameLast {A : Set} : List⁺ A → List⁺ A → Set where
  [-]ₛₗ : ∀ {a : A} → SameLast (a ⁺∷ []) (a ⁺∷ [])
  _∷ₛₗₗ_ : ∀ {l₁ l₂ : List⁺ A} (a : A) → SameLast l₁ l₂ → SameLast (a ∷⁺ l₁) l₂
  _∷ₛₗᵣ_ : ∀ {l₁ l₂ : List⁺ A} (a : A) → SameLast l₁ l₂ → SameLast l₁ (a ∷⁺ l₂)

same-last-lemm₁ : ∀ {A : Set} {l : List A} {a : A} → SameLast (a ⁺∷ l) (a ⁺∷ l)
same-last-lemm₁ {l = []} = [-]ₛₗ
same-last-lemm₁ {l = _ ∷ l} {a = a} = a ∷ₛₗₗ (a ∷ₛₗᵣ same-last-lemm₁)

same-last-lemm₂ : ∀ {A : Set} {l₁ l₂ : List⁺ A} → SameLast l₁ l₂ → SameLast l₂ l₁
same-last-lemm₂ [-]ₛₗ = [-]ₛₗ
same-last-lemm₂ (a ∷ₛₗₗ sameLast) = a ∷ₛₗᵣ same-last-lemm₂ sameLast
same-last-lemm₂ (a ∷ₛₗᵣ sameLast) = a ∷ₛₗₗ same-last-lemm₂ sameLast

same-last-lemm₃ : ∀ {A : Set} {a : A} {l₁ l₂ : List⁺ A} → SameLast (a ∷⁺ l₁) l₂ → SameLast l₁ l₂
same-last-lemm₃ (_ ∷ₛₗₗ sameLast) = sameLast
same-last-lemm₃ (a ∷ₛₗᵣ sameLast) = a ∷ₛₗᵣ same-last-lemm₃ sameLast

same-last-lemm₄ : ∀ {A : Set} {l₁ l₂ l₃ : List⁺ A} → SameLast l₁ l₂ → SameLast l₂ l₃ → SameLast l₁ l₃
same-last-lemm₄ [-]ₛₗ b = b
same-last-lemm₄ (x ∷ₛₗₗ a) b = x ∷ₛₗₗ same-last-lemm₄ a b
same-last-lemm₄ (x ∷ₛₗᵣ a) (.x ∷ₛₗₗ b) = same-last-lemm₄ a b
same-last-lemm₄ {l₂ = .x ⁺∷ z ∷ l₂} (x ∷ₛₗᵣ a) (y ∷ₛₗᵣ b) = y ∷ₛₗᵣ same-last-lemm₄ a (same-last-lemm₃ b)

-- Removes intersections from a chain.
flatten : (chain₁ : List⁺ Pos) → IsChain⁺ chain₁ → ∃[ chain₂ ] (IsChain⁺ chain₂ × SameHead chain₁ chain₂ × SameLast chain₁ chain₂)
flatten (pos ⁺∷ []) [-] = ⟨ pos ⁺∷ [] , ⟨ [-] , ⟨ refl , [-]ₛₗ ⟩ ⟩ ⟩
flatten (pos₁ ⁺∷ pos₂ ∷ chain) (adj ∷ₗ chainAdj₁) with flatten (pos₂ ⁺∷ chain) chainAdj₁
... | ⟨ .pos₂ ⁺∷ chain₂ , ⟨ chainAdj₂ , ⟨ refl , sameLast ⟩ ⟩ ⟩ = ⟨ _
                                                                  , ⟨ proj₁ (proj₂ flattened)
                                                                    , ⟨ refl
                                                                      , pos₁ ∷ₛₗₗ same-last-lemm₄ sameLast (proj₂ (proj₂ flattened))
                                                                      ⟩
                                                                    ⟩
                                                                  ⟩
  where flatten‵ : (chain₁ : List⁺ Pos) → IsChain⁺ chain₁ → Maybe (∃[ chain₂ ] (IsChain⁺ (pos₁ ⁺∷ chain₂) × SameLast chain₁ (pos₁ ⁺∷ chain₂)))
        flatten‵ (pos ⁺∷ []) [-] with pos ≟ₚₒₛ pos₁
        ... | false because _ = nothing
        ... | true because ofʸ refl = just ⟨ [] , ⟨ [-] , [-]ₛₗ ⟩ ⟩
        flatten‵ (pos₃ ⁺∷ pos₄ ∷ t) (adj ∷ₗ chainAdj) with pos₃ ≟ₚₒₛ pos₁
        ... | false because _ = Maybe.map (λ{⟨ chain , ⟨ isChain , sameLast ⟩ ⟩ → ⟨ chain , ⟨ isChain , pos₃ ∷ₛₗₗ sameLast ⟩ ⟩}) $ flatten‵ (pos₄ ⁺∷ t) chainAdj
        ... | true because ofʸ refl = just ⟨ pos₄ ∷ t , ⟨ adj ∷ₗ chainAdj , pos₃ ∷ₛₗₗ (pos₃ ∷ₛₗᵣ same-last-lemm₁) ⟩ ⟩
        flattened = Maybe.fromMaybe ⟨ pos₂ ∷ chain , ⟨ adj ∷ₗ chainAdj₁ , pos₁ ∷ₛₗᵣ same-last-lemm₂ sameLast ⟩ ⟩ $ flatten‵ (pos₂ ⁺∷ chain₂) chainAdj₂

{-# NON_TERMINATING #-}
buildChain : Field → (startPos nextPos : Pos) → Adjacent startPos nextPos → Player → Maybe (∃[ chain ] IsChain⁺ chain)
buildChain fld startPos nextPos adj player = just chain₂ -- TODO: check square
  where getNextPlayerPos : (pos₁ : Pos) → Direction → ∃[ pos₂ ] Adjacent pos₁ pos₂
        getNextPlayerPos centerPos dir with direction→pos dir centerPos
        ... | nothing = getNextPlayerPos centerPos $ rotate dir -- TODO: use filter + maybe′ ?
        ... | just ⟨ pos , adj ⟩ = if ⌊ pos ≟ₚₒₛ startPos ⌋ ∨ (isPlayer fld pos player) then ⟨ pos , adj ⟩
                                   else (getNextPlayerPos centerPos $ rotate dir)
        getChain : (startPos‵ nextPos‵ : Pos) → Adjacent startPos‵ nextPos‵ → ∃[ chain ] (IsChain⁺ (startPos‵ ∷⁺ chain) × IsRing⁺ (startPos ∷⁺ chain))
        getChain _ nextPos adj = let ⟨ nextPos‵ , nextAdj ⟩ = getNextPlayerPos nextPos (rotate¬adjacent (inverse (direction adj)))
                                     ⟨ nextChain , ⟨ nextChainAdj , nextRing ⟩ ⟩ = getChain nextPos nextPos‵ nextAdj
                                 in case nextPos‵ ≟ₚₒₛ startPos of
                                    λ { (true because ofʸ proof) → ⟨ nextPos ⁺∷ [] , ⟨ adj ∷ₗ [-] , ring-init (adj↔ (subst (Adjacent nextPos) proof nextAdj)) ⟩ ⟩
                                      ; (false because _) → ⟨ nextPos ∷⁺ nextChain , ⟨ adj ∷ₗ nextChainAdj , ring-extend nextRing ⟩ ⟩
                                      }
        chain₁ : ∃[ chain ] (IsChain⁺ chain × IsRing⁺ chain)
        chain₁ = ⟨ _ , proj₂ (getChain startPos nextPos adj) ⟩
        chain₂ : ∃[ chain ] IsChain⁺ chain
        chain₂ = map₂ proj₁ $ flatten (proj₁ chain₁) (proj₁ (proj₂ chain₁))

posInsideRing : Pos → List Pos → Bool
posInsideRing pos ring = intersectionsCount ring $ firstIntersectionState $ List.reverse ring
  where open import Data.Fin.Properties using (_≤?_)
        open import Data.Fin.Patterns
        open import Data.Fin using (suc)
        data IntersectionState : Set where
          is↑ : IntersectionState
          is↔ : IntersectionState
          is↓ : IntersectionState
          is× : IntersectionState
        intersectionState : Pos → Pos → IntersectionState
        intersectionState ⟨ x₁ , y₁ ⟩ ⟨ x₂ , y₂ ⟩ = if ⌊ x₁ ≤? x₂ ⌋ then intersectionState‵ y₁ y₂ else is×
          where intersectionState‵ : ∀ {n} → Fin n → Fin n → IntersectionState
                intersectionState‵ 0F 0F = is↔
                intersectionState‵ 1F 0F = is↑
                intersectionState‵ 0F 1F = is↓
                intersectionState‵ 0F (suc (suc _)) = is×
                intersectionState‵ (suc (suc _)) 0F = is×
                intersectionState‵ (suc y₁) (suc y₂) = intersectionState‵ y₁ y₂
        firstIntersectionState : List Pos → IntersectionState
        firstIntersectionState [] = is×
        firstIntersectionState (pos₂ ∷ tail) with intersectionState pos pos₂
        ... | is↔ = firstIntersectionState tail
        ... | is = is
        intersectionsCount : List Pos → IntersectionState → Bool
        intersectionsCount [] _ = false
        intersectionsCount (pos₂ ∷ tail) is with intersectionState pos pos₂
        intersectionsCount (_ ∷ tail) is↓ | is↑ = not $ intersectionsCount tail is↑
        intersectionsCount (_ ∷ tail) is↑ | is↓ = not $ intersectionsCount tail is↓
        intersectionsCount (_ ∷ tail) is | is↔ = intersectionsCount tail is
        intersectionsCount (_ ∷ tail) _ | is = intersectionsCount tail is
