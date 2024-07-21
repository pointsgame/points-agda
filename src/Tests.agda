module Tests where

open import Data.Bool using (not; true; false; if_then_else_)
open import Data.Bool.Properties using (T?)
open import Data.Char as Char using (Char)
open import Data.Fin using (Fin)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Sort.MergeSort as Sort
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Nat.Properties as NatProperties
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.Construct.On as On
open import Data.String as String using (String)
open import Function using (_$_; _∘_; case_of_)
open import Relation.Nullary using (_because_; ofʸ)
open import Relation.Nullary.Decidable using (¬?)

open import Player
open import Field

record GenField : Set where
  field
    width height : ℕ
    fld : Field {width} {height}

constructField : String → Maybe GenField
constructField image with List.filter (λ s → ¬? (s String.≟ "")) $ String.wordsBy (Char._≟ '\n') image
... | [] = nothing
... | lines @ (h ∷ _) =
  let width = String.length h
      height = List.length lines
      moves = List.map (λ{(c , pos) → (if Char.isLower c then Red else Black) , pos}) $
              Sort.sort (On.decTotalOrder NatProperties.≤-decTotalOrder (Char.toℕ ∘ Char.toLower ∘ proj₁)) $
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

simpleSurroundImage = constructField "
.a.
cBa
.a.
"

surroundEmptyTerritoryImage = constructField "
.a.
a.a
.a.
"

movePriorityImage = constructField "
.aB.
aCaB
.aB.
"

movePriorityBigImage = constructField "
.B..
BaB.
aCaB
.aB.
"

onionSurroundingsImage = constructField "
...c...
..cBc..
.cBaBc.
..cBc..
...c...
"

deepOnionSurroundingsImage = constructField "
...D...
..DcD..
.DcBcD.
DcBaBcD
.DcBcD.
..DcD..
...D...
"

applyControlSurroundingInSameTurnImage = constructField "
.a.
aBa
.a.
"

doubleSurroundImage = constructField "
.a.a.
aAbAa
.a.a.
"

doubleSurroundWithEmptyPartImage = constructField "
.b.b..
b.zAb.
.b.b..
"

shouldNotLeaveEmptyInsideImage = constructField "
.aaaa..
a....a.
a.b...a
.z.bC.a
a.b...a
a....a.
.aaaa..
"

surroundInOppositeTurnImage = constructField "
.a.
aBa
.a.
"

partlySurroundInOppositeTurnImage = constructField "
.a..
aBa.
.a.a
..a.
"

holeInsideSurroundingImage = constructField "
....c....
...c.c...
..c...c..
.c..a..c.
c..a.a..c
.c..a..c.
..c...c..
...cBc...
....d....
"

holeInsideSurroundingAfterOppositeTurnSurroundingImage = constructField "
....b....
...b.b...
..b...b..
.b..a..b.
b..a.a..b
.b..a..b.
..b...b..
...bCb...
....b....
"

surroundingDoesNotExpandImage = constructField "
....a....
...a.a...
..a.a.a..
.a.a.a.a.
a.a.aBa.a
.a.a.a.a.
..a.a.a..
...a.a...
....a....
"

twoSurroundingsWithCommonBorderImage = constructField "
.a..
aAa.
.bAa
..a.
"

twoSurroundingsWithCommonDotImage = constructField "
.a.a.
aBcBa
.a.a.
"

threeSurroundingsWithCommonBordersImage = constructField "
..a..
.aAa.
..bAa
.aAa.
..a..
"

twoSurroundingsWithCommonDotOneBorderlineEmptyPlaceImage = constructField "
..a..
.aBa.
..c.a
.aBa.
..a..
"
