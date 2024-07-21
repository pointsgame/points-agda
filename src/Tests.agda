open import Data.Bool using (not; true; false; if_then_else_)
open import Data.Bool.Properties using (T?)
open import Data.Char as Char using (Char)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String)
open import Function using (_$_; _∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (_because_; ofʸ)
open import Relation.Nullary.Decidable using (¬?)

open import Player
open import Field

record GenField : Set where
  field
    width height : ℕ
    fld : Field {width} {height}

insert : ∀ {width height} → List (Char × Fin width × Fin height) → (Char × Fin width × Fin height) → List (Char × Fin width × Fin height)
insert [] n = n ∷ []
insert (h @ (hc , _) ∷ l) e @ (ec , _) with Char.toℕ (Char.toLower ec) ≤? Char.toℕ (Char.toLower hc)
... | false because _ = e ∷ h ∷ l
... | true because _ = h ∷ insert l e

sort : ∀ {width height} → List (Char × Fin width × Fin height) → List (Char × Fin width × Fin height)
sort = List.foldl insert []

constructField : String → Maybe GenField
constructField image with List.filter (λ s → ¬? (s String.≟ "")) $ String.wordsBy (Char._≟ '\n') image
... | [] = nothing
... | lines @ (h ∷ _) =
  let width = String.length h
      height = List.length lines
      moves = List.map (λ{(c , pos) → (if Char.isLower c then Red else Black) , pos}) $
              sort $
              List.filter (λ{(c , _) → ¬? (Char.toLower c Char.≟ Char.toUpper c)}) $
              List.concatMap (λ{(line , y) → List.map (λ{(c , x) → c , x , y}) $
                                             List.zip (String.toList line) $
                                             List.allFin width}) $
              List.zip lines $
              List.allFin height
      fld = List.foldl (λ { (just fld) (player , pos) → case T? (isPuttingAllowed fld pos) of
                                                        λ { (false because _) → nothing
                                                          ; (true because ofʸ proof) → just (putPoint pos player fld proof)
                                                          }
                          ; nothing _ → nothing
                          }) (just emptyField) moves
  in Maybe.map (λ fld → record { fld = fld }) fld

simpleSurround = GenField.fld $ Maybe.from-just $ constructField "
.a.
cBa
.a.
"

_ : Field.scoreRed simpleSurround ≡ 1
_ = refl

_ : Field.scoreBlack simpleSurround ≡ 0
_ = refl

_ : isPuttingAllowed simpleSurround (0F , 0F) ≡ true
_ = refl

_ : isPuttingAllowed simpleSurround (1F , 1F) ≡ false
_ = refl
