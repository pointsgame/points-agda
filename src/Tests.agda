{-# OPTIONS --erasure #-}

module Tests where

open import Data.Bool using (not; true; false; if_then_else_)
open import Data.Bool.Properties using (T?)
open import Data.Char as Char using (Char)
open import Data.Fin.Patterns
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

surroundEmptyTerritory = GenField.fld $ Maybe.from-just $ constructField "
.a.
a.a
.a.
"

_ : Field.scoreRed surroundEmptyTerritory ≡ 0
_ = refl

_ : Field.scoreBlack surroundEmptyTerritory ≡ 0
_ = refl

movePriority = GenField.fld $ Maybe.from-just $ constructField "
.aB.
aCaB
.aB.
"

_ : Field.scoreRed movePriority ≡ 0
_ = refl

_ : Field.scoreBlack movePriority ≡ 1
_ = refl

movePriorityBig = GenField.fld $ Maybe.from-just $ constructField "
.B..
BaB.
aCaB
.aB.
"

_ : Field.scoreRed movePriorityBig ≡ 0
_ = refl

_ : Field.scoreBlack movePriorityBig ≡ 2
_ = refl

onionSurroundings = GenField.fld $ Maybe.from-just $ constructField "
...c...
..cBc..
.cBaBc.
..cBc..
...c...
"

_ : Field.scoreRed onionSurroundings ≡ 4
_ = refl

_ : Field.scoreBlack onionSurroundings ≡ 0
_ = refl

deepOnionSurroundings = GenField.fld $ Maybe.from-just $ constructField "
...D...
..DcD..
.DcBcD.
DcBaBcD
.DcBcD.
..DcD..
...D...
"

_ : Field.scoreRed deepOnionSurroundings ≡ 0
_ = refl

_ : Field.scoreBlack deepOnionSurroundings ≡ 9
_ = refl

applyControlSurroundingInSameTurn = GenField.fld $ Maybe.from-just $ constructField "
.a.
aBa
.a.
"

_ : Field.scoreRed applyControlSurroundingInSameTurn ≡ 1
_ = refl

_ : Field.scoreBlack applyControlSurroundingInSameTurn ≡ 0
_ = refl

doubleSurround = GenField.fld $ Maybe.from-just $ constructField "
.a.a.
aAbAa
.a.a.
"

_ : Field.scoreRed doubleSurround ≡ 2
_ = refl

_ : Field.scoreBlack doubleSurround ≡ 0
_ = refl

doubleSurroundWithEmptyPart = GenField.fld $ Maybe.from-just $ constructField "
.b.b..
b.zAb.
.b.b..
"

_ : Field.scoreRed doubleSurroundWithEmptyPart ≡ 1
_ = refl

_ : Field.scoreBlack doubleSurroundWithEmptyPart ≡ 0
_ = refl

shouldNotLeaveEmptyInside = GenField.fld $ Maybe.from-just $ constructField "
.aaaa..
a....a.
a.b...a
.z.bC.a
a.b...a
a....a.
.aaaa..
"

_ : Field.scoreRed shouldNotLeaveEmptyInside ≡ 1
_ = refl

_ : Field.scoreBlack shouldNotLeaveEmptyInside ≡ 0
_ = refl

surroundInOppositeTurn = GenField.fld $ Maybe.from-just $ constructField "
.a.
aBa
.a.
"

_ : Field.scoreRed surroundInOppositeTurn ≡ 1
_ = refl

_ : Field.scoreBlack surroundInOppositeTurn ≡ 0
_ = refl

partlySurroundInOppositeTurn = GenField.fld $ Maybe.from-just $ constructField "
.a..
aBa.
.a.a
..a.
"

_ : Field.scoreRed partlySurroundInOppositeTurn ≡ 1
_ = refl

_ : Field.scoreBlack partlySurroundInOppositeTurn ≡ 0
_ = refl

holeInsideSurrounding = GenField.fld $ Maybe.from-just $ constructField "
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

_ : Field.scoreRed holeInsideSurrounding ≡ 1
_ = refl

_ : Field.scoreBlack holeInsideSurrounding ≡ 0
_ = refl

holeInsideSurroundingAfterOppositeTurnSurrounding = GenField.fld $ Maybe.from-just $ constructField "
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

_ : Field.scoreRed holeInsideSurroundingAfterOppositeTurnSurrounding ≡ 1
_ = refl

_ : Field.scoreBlack holeInsideSurroundingAfterOppositeTurnSurrounding ≡ 0
_ = refl

surroundingDoesNotExpand = GenField.fld $ Maybe.from-just $ constructField "
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

_ : Field.scoreRed surroundingDoesNotExpand ≡ 1
_ = refl

_ : Field.scoreBlack surroundingDoesNotExpand ≡ 0
_ = refl

twoSurroundingsWithCommonBorder = GenField.fld $ Maybe.from-just $ constructField "
.a..
aAa.
.bAa
..a.
"

_ : Field.scoreRed twoSurroundingsWithCommonBorder ≡ 2
_ = refl

_ : Field.scoreBlack twoSurroundingsWithCommonBorder ≡ 0
_ = refl

twoSurroundingsWithCommonDot = GenField.fld $ Maybe.from-just $ constructField "
.a.a.
aBcBa
.a.a.
"

_ : Field.scoreRed twoSurroundingsWithCommonDot ≡ 2
_ = refl

_ : Field.scoreBlack twoSurroundingsWithCommonDot ≡ 0
_ = refl

threeSurroundingsWithCommonBorders = GenField.fld $ Maybe.from-just $ constructField "
..a..
.aAa.
..bAa
.aAa.
..a..
"

_ : Field.scoreRed threeSurroundingsWithCommonBorders ≡ 3
_ = refl

_ : Field.scoreBlack threeSurroundingsWithCommonBorders ≡ 0
_ = refl

twoSurroundingsWithCommonDotOneBorderlineEmptyPlace = GenField.fld $ Maybe.from-just $ constructField "
..a..
.aBa.
..c.a
.aBa.
..a..
"

_ : Field.scoreRed twoSurroundingsWithCommonDotOneBorderlineEmptyPlace ≡ 2
_ = refl

_ : Field.scoreBlack twoSurroundingsWithCommonDotOneBorderlineEmptyPlace ≡ 0
_ = refl
