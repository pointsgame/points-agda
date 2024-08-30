{-# OPTIONS --guardedness #-}

module Bench where

open import Data.Bool using (true; false)
open import Data.Bool.Properties using (T?)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties using (*↔×)
open import Data.List as List using ()
open import Data.Maybe as Maybe using (nothing; just)
open import Data.Nat as ℕ using (ℕ; _*_; _+_)
open import Data.Nat.PseudoRandom.LCG using (step; glibc)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Function using (_$_; case_of_)
open import Relation.Nullary using (_because_; ofʸ)

open import Player
open import Field

swap : ∀ {A : Set} {n : ℕ} → Fin (ℕ.suc n) → Vec A (ℕ.suc n) → A × Vec A n
swap Fin.zero (x₀ ∷ xs) = x₀ , xs
swap {A = A} (Fin.suc i) (x₀ ∷ xs) = go i xs
  where
    go : ∀ {n} → Fin n → Vec A n → A × Vec A n
    go Fin.zero (x ∷ xs) = x , x₀ ∷ xs
    go (Fin.suc i) (x ∷ xs) with go i xs
    ... | (x′ , xs′) = x′ , x ∷ xs′

allMoves : {width height : ℕ} → Vec (Pos {width} {height}) (width * height)
allMoves {width} {height} = Vec.map (Function.Inverse.to *↔×) $ Vec.allFin (width * height)

module RandomState (step : ℕ → ℕ) where
  open import Effect.Monad.State
  open import Effect.Monad
  open RawMonadState (monadState {_} {ℕ})
  open RawMonad (monad {_} {ℕ})

  randomℕ : State ℕ ℕ
  randomℕ = modify step ⊛> get

  open import Data.Nat.DivMod using (_mod_)

  randomFin : ∀ {n : ℕ} → State ℕ $ Fin $ ℕ.suc n
  randomFin = (_mod _) <$> randomℕ

  shuffle : ∀ {A : Set} {n : ℕ} → Vec A n → State ℕ (Vec A n)
  shuffle [] = pure []
  shuffle {n = ℕ.suc n} xs@(_ ∷ _) = do
    k ← randomFin
    let (x′ , xs′) = swap k xs
    xs″ ← shuffle xs′
    pure (x′ ∷ xs″)

  randomGame : (width height : ℕ) → State ℕ $ Field {width} {height}
  randomGame width height = do
    moves ← shuffle allMoves
    pure $ List.foldl (λ { fld pos → case T? (isPuttingAllowed fld pos) of
                                        λ { (false because _) → fld
                                          ; (true because ofʸ proof) → putNextPoint pos fld proof
                                          }
                         }) emptyField $ Vec.toList moves

  import Data.Vec.Effectful as VecEff
  open VecEff.TraversableM (monad {_} {ℕ})

  randomGames : (n width height : ℕ) → State ℕ $ Vec (Field {width} {height}) n
  randomGames n width height = sequenceM $ Vec.replicate n $ randomGame width height

open RandomState (step glibc)

open import Effect.Monad.State using (evalState)

games : ℕ → (n width height : ℕ) → Vec Field n
games seed n width height = evalState (randomGames n width height) seed

record Result : Set where
  field
    red black : ℕ

gameResult : {width height : ℕ} -> Field {width} {height} → Result
gameResult fld with winner fld
... | just Player.Red = record { red = 1; black = 0 }
... | just Player.Black = record { red = 0; black = 1 }
... | nothing = record { red = 0; black = 0 }

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Bundles using (RawMonoid)

result-rawMonoid : RawMonoid _ _
result-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = λ a b → record { red = Result.red a + Result.red b; black = Result.black a + Result.black b }
  ; ε = record { red = 0; black = 0 }
  }

open import Data.Nat.Show using (show)
open import Data.String using (_++_)
open import IO as IO using (IO; Main; run; pure; putStrLn)

main : Main
main = run do
  let result = Vec.foldl₁ (RawMonoid._∙_ result-rawMonoid) $ Vec.map gameResult $ games 7 100 10 10
  putStrLn $ (show $ Result.red result) ++ "|" ++ (show $ Result.black result)