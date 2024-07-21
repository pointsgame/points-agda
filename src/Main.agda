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

onionSurroundings : IO {0ℓ} ⊤
onionSurroundings = test "onion surroundings" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 4 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false onionSurroundingsImage

deepOnionSurroundings : IO {0ℓ} ⊤
deepOnionSurroundings = test "deep onion surroundings" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 0 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 9 ⌋
  ) false deepOnionSurroundingsImage

applyControlSurroundingInSameTurn : IO {0ℓ} ⊤
applyControlSurroundingInSameTurn = test "apply 'control' surrounding in same turn" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false applyControlSurroundingInSameTurnImage

doubleSurround : IO {0ℓ} ⊤
doubleSurround = test "double surround" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 2 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false doubleSurroundImage

doubleSurroundWithEmptyPart : IO {0ℓ} ⊤
doubleSurroundWithEmptyPart = test "double surround with empty part" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false doubleSurroundWithEmptyPartImage

shouldNotLeaveEmptyInside : IO {0ℓ} ⊤
shouldNotLeaveEmptyInside = test "should not leave empty inside" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false shouldNotLeaveEmptyInsideImage

surroundInOppositeTurn : IO {0ℓ} ⊤
surroundInOppositeTurn = test "surround in opposite turn" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false surroundInOppositeTurnImage

partlySurroundInOppositeTurn : IO {0ℓ} ⊤
partlySurroundInOppositeTurn = test "partly surround in opposite turn" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false partlySurroundInOppositeTurnImage

holeInsideSurrounding : IO {0ℓ} ⊤
holeInsideSurrounding = test "a hole inside a surrounding" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false holeInsideSurroundingImage

holeInsideSurroundingAfterOppositeTurnSurrounding : IO {0ℓ} ⊤
holeInsideSurroundingAfterOppositeTurnSurrounding = test "a hole inside a surrounding, after opposite turn surrounding" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false holeInsideSurroundingAfterOppositeTurnSurroundingImage

surroundingDoesNotExpand : IO {0ℓ} ⊤
surroundingDoesNotExpand = test "surrounding does not expand" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 1 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false surroundingDoesNotExpandImage

twoSurroundingsWithCommonBorder : IO {0ℓ} ⊤
twoSurroundingsWithCommonBorder = test "2 surroundings with common border" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 2 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false twoSurroundingsWithCommonBorderImage

twoSurroundingsWithCommonDot : IO {0ℓ} ⊤
twoSurroundingsWithCommonDot = test "2 surroundings with common dot" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 2 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false twoSurroundingsWithCommonDotImage

threeSurroundingsWithCommonBorders : IO {0ℓ} ⊤
threeSurroundingsWithCommonBorders = test "3 surroundings with common borders" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 3 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false threeSurroundingsWithCommonBordersImage

twoSurroundingsWithCommonDotOneBorderlineEmptyPlace : IO {0ℓ} ⊤
twoSurroundingsWithCommonDotOneBorderlineEmptyPlace = test "2 surroundings with common dot, one borderline empty place" $ Maybe.maybe′ (λ genField →
  let fld = GenField.fld genField
  in
    ⌊ Field.scoreRed (GenField.fld genField) ℕ.≟ 2 ⌋ ∧
    ⌊ Field.scoreBlack (GenField.fld genField) ℕ.≟ 0 ⌋
  ) false twoSurroundingsWithCommonDotOneBorderlineEmptyPlaceImage

main : Main
main = run do
  simpleSurround
  surroundEmptyTerritory
  movePriority
  movePriorityBig
  onionSurroundings
  deepOnionSurroundings
  applyControlSurroundingInSameTurn
  doubleSurround
  doubleSurroundWithEmptyPart
  shouldNotLeaveEmptyInside
  surroundInOppositeTurn
  partlySurroundInOppositeTurn
  holeInsideSurrounding
  holeInsideSurroundingAfterOppositeTurnSurrounding
  surroundingDoesNotExpand
  twoSurroundingsWithCommonBorder
  twoSurroundingsWithCommonDot
  threeSurroundingsWithCommonBorders
  twoSurroundingsWithCommonDotOneBorderlineEmptyPlace
