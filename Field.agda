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
open import Function using (_$_; _∘_)
open import Generic.Main using (_==_)
open import Relation.Binary.PropositionalEquality using (refl)
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
getFirstNextPos adj = {!!}

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

IsChain : List Pos → Set
IsChain = Linked Adjacent

data SameHead {A : Set} : List A → List A → Set where
  []ₛₕ : SameHead [] []
  _∷ₛₕ_ : ∀ {a : A} (l₁ l₂ : List A) → SameHead (a ∷ l₁) (a ∷ l₂)

-- Removes intersections from a chain.
-- SameHead is necessary for recursion over linked list.
flatten : (chain₁ : List Pos) → IsChain chain₁ → ∃[ chain₂ ] (IsChain chain₂ × SameHead chain₁ chain₂)
flatten [] []ₗ = ⟨ _ , ⟨ []ₗ , []ₛₕ ⟩ ⟩
flatten (pos ∷ []) [-] = ⟨ pos ∷ [] , ⟨ [-] , [] ∷ₛₕ [] ⟩ ⟩
flatten (pos₁ ∷ pos₂ ∷ chain) (adj ∷ₗ chainAdj₁) with flatten (pos₂ ∷ chain) chainAdj₁
... | ⟨ .(pos₂ ∷ chain₂) , ⟨ chainAdj₂ , .chain ∷ₛₕ chain₂ ⟩ ⟩ = ⟨ _ , ⟨ proj₂ flattened , (pos₂ ∷ chain) ∷ₛₕ proj₁ flattened ⟩ ⟩
  where flatten‵ : (chain₁ : List Pos) → IsChain chain₁ → ∃[ chain₂ ] IsChain (pos₁ ∷ chain₂)
        flatten‵ [] []ₗ = ⟨ pos₂ ∷ chain , adj ∷ₗ chainAdj₁ ⟩
        flatten‵ (pos ∷ []) [-] with pos ≟ₚₒₛ pos₁
        ... | false because _ = ⟨ pos₂ ∷ chain , adj ∷ₗ chainAdj₁ ⟩
        ... | true because ofʸ refl = ⟨ [] , [-] ⟩
        flatten‵ (pos₃ ∷ pos₄ ∷ t) (adj ∷ₗ chainAdj) with pos₃ ≟ₚₒₛ pos₁
        ... | false because _ = flatten‵ (pos₄ ∷ t) chainAdj
        ... | true because ofʸ refl = ⟨ pos₄ ∷ t , adj ∷ₗ chainAdj ⟩
        flattened = flatten‵ (pos₂ ∷ chain₂) chainAdj₂

{-# NON_TERMINATING #-}
buildChain : Field → (startPos nextPos : Pos) → Adjacent startPos nextPos → Player → Maybe (∃[ chain ] IsChain chain)
buildChain fld startPos nextPos adj player = just chain₂ -- TODO: check square
  where getNextPlayerPos : (pos₁ : Pos) → Direction → ∃[ pos₂ ] Adjacent pos₁ pos₂
        getNextPlayerPos centerPos dir with direction→pos dir centerPos
        ... | nothing = getNextPlayerPos centerPos $ rotate dir -- TODO: use filter + maybe′ ?
        ... | just ⟨ pos , adj ⟩ = if ⌊ pos ≟ₚₒₛ startPos ⌋ ∨ (isPlayer fld pos player) then ⟨ pos , adj ⟩
                                   else (getNextPlayerPos centerPos $ rotate dir)
        getChain : (startPos nextPos : Pos) → Adjacent startPos nextPos → ∃[ chain ] IsChain (startPos ∷ chain)
        getChain _ nextPos adj = let ⟨ nextPos‵ , nextAdj ⟩ = getNextPlayerPos nextPos (rotate¬adjacent (inverse (direction adj)))
                                     ⟨ nextChain , nextChainAdj ⟩ = getChain nextPos nextPos‵ nextAdj
                                 in if ⌊ nextPos‵ ≟ₚₒₛ startPos ⌋ then ⟨ nextPos ∷ [] , adj ∷ₗ [-] ⟩
                                    else ⟨ nextPos ∷ nextChain , adj ∷ₗ nextChainAdj ⟩
        chain₁ : ∃[ chain ] IsChain chain
        chain₁ = ⟨ _ , proj₂ (getChain startPos nextPos adj) ⟩
        chain₂ : ∃[ chain ] IsChain chain
        chain₂ = map₂ proj₁ $ flatten (proj₁ chain₁) (proj₂ chain₁)
