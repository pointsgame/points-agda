open import Data.Nat as Nat using (ℕ)

module Field {width height : ℕ} where

open import Data.Bool as Bool
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _∘_)
open import Generic.Main using (_==_)

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
        neighborhood pos = List.mapMaybe Function.id $ Maybe.map proj₁ (n pos)
                                                     ∷ Maybe.map proj₁ (s pos)
                                                     ∷ Maybe.map proj₁ (w pos)
                                                     ∷ Maybe.map proj₁ (e pos)
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
