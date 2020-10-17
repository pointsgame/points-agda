module Player where

open import Generic.Main using (Eq; deriveEqTo)

data Player : Set where
  Red : Player
  Black : Player

instance PlayerEq : Eq Player
unquoteDef PlayerEq = deriveEqTo PlayerEq (quote Player)

next : Player → Player
next Red = Black
next Black = Red
