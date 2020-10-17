module Point where

open import Data.Bool
open import Generic.Main using (Eq; viaBase; deriveEqTo; _==_)
open import Player

instance
  BoolEq : Eq Bool
  BoolEq = viaBase _≟_

data Point : Set where
  EmptyPoint : Point
  PlayerPoint : Player → Point
  BasePoint : Player → Bool → Point
  EmptyBasePoint : Player → Point

instance PointEq : Eq Point
unquoteDef PointEq = deriveEqTo PointEq (quote Point)
