module TypelevelTests where

open import Data.Bool using (true; false)
open import Data.Fin.Patterns
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Field
open import Tests

_ : Field.scoreRed simpleSurround ≡ 1
_ = refl

_ : Field.scoreBlack simpleSurround ≡ 0
_ = refl

_ : isPuttingAllowed simpleSurround (0F , 0F) ≡ true
_ = refl

_ : isPuttingAllowed simpleSurround (1F , 1F) ≡ false
_ = refl
