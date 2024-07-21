{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool using (Bool; false; if_then_else_; not; _∧_)
open import Data.Fin.Patterns
open import Data.Maybe as Maybe
open import Data.Nat as ℕ
open import Data.Product using (_,_)
open import Data.String as String
open import Data.Unit.Polymorphic using (⊤)
open import Function using (_$_)
open import IO
open import Level
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Field
open import Tests

test : String → Bool → IO {0ℓ} ⊤
test name cond = do
  putStr name
  putStr ": "
  putStrLn (if cond then "passed" else "failed")

simpleSurround : IO {0ℓ} ⊤
simpleSurround = test "simple surround" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false simpleSurroundImage

surroundEmptyTerritory : IO {0ℓ} ⊤
surroundEmptyTerritory = test "surround empty territory" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 0 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false surroundEmptyTerritoryImage

movePriority : IO {0ℓ} ⊤
movePriority = test "move priority" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 0 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 1 ⌋
  ) false movePriorityImage

movePriorityBig : IO {0ℓ} ⊤
movePriorityBig = test "move priority, big" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 0 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 2 ⌋
  ) false movePriorityBigImage

main : Main
main = run do
  simpleSurround
  surroundEmptyTerritory
  movePriority
  movePriorityBig
