{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool using (Bool; if_then_else_; not; _∧_)
open import Data.Fin.Patterns
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

simpleSurroundTest : IO {0ℓ} ⊤
simpleSurroundTest = test "simple surround" $
  ⌊ Field.scoreRed simpleSurround ℕ.≟ 1 ⌋ ∧
  ⌊ Field.scoreBlack simpleSurround ℕ.≟ 0 ⌋ ∧
  isPuttingAllowed simpleSurround (0F , 0F) ∧
  not (isPuttingAllowed simpleSurround (1F , 1F))

main : Main
main = run do simpleSurroundTest
