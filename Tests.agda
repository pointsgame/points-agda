open import Data.Bool using (not; true; false; if_then_else_)
open import Data.Char as Char using (Char)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String as String using (String)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (_because_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Player
open import Field

record GenField : Set where
  field
    width height : ℕ
    fld : Field {width} {height}

insert : ∀ {width height} → List (Char × Fin width × Fin height) → (Char × Fin width × Fin height) → List (Char × Fin width × Fin height)
insert [] n = n ∷ []
insert (h @ (⟨ hc , _ ⟩) ∷ l) e @ (⟨ ec , _ ⟩) with Char.toℕ (Char.toLower ec) ≤? Char.toℕ (Char.toLower hc)
... | false because _ = e ∷ h ∷ l
... | true because _ = h ∷ insert l e

sort : ∀ {width height} → List (Char × Fin width × Fin height) → List (Char × Fin width × Fin height)
sort = List.foldl insert []

constructField : String → Maybe GenField
constructField image with List.boolFilter (λ s → not ⌊ s String.≟ "" ⌋) $ String.wordsBy (Char._≟ '\n') image
... | [] = nothing
... | lines @ (h ∷ _) =
  let width = String.length h
      height = List.length lines
      moves = List.map (λ{⟨ c , pos ⟩ → ⟨ if Char.isLower c then Red else Black , pos ⟩}) $
              sort $
              List.boolFilter (λ{⟨ c , _ ⟩ → not ⌊ Char.toLower c Char.≟ Char.toUpper c ⌋}) $
              List.concatMap (λ{⟨ line , y ⟩ → List.map (λ{⟨ c , x ⟩ → ⟨ c , ⟨ x , y ⟩ ⟩}) $
                                               List.zip (String.toList line) $
                                               List.allFin width}) $
              List.zip lines $
              List.allFin height
      fld = List.foldl (λ{fld → λ{⟨ player , pos ⟩ → putPoint pos player fld }}) emptyField moves
  in just record { width = width ; height = height ; fld = fld }

simpleSurround = GenField.fld $ Maybe.from-just $ constructField "
.a.
cBa
.a.
"

_ : Field.scoreRed simpleSurround ≡ 1
_ = refl

_ : Field.scoreBlack simpleSurround ≡ 0
_ = refl

_ : isPuttingAllowed simpleSurround ⟨ 0F , 0F ⟩ ≡ true
_ = refl

_ : isPuttingAllowed simpleSurround ⟨ 1F , 1F ⟩ ≡ false
_ = refl
