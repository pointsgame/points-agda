open import Data.Nat as ℕ using (ℕ)

module Field {width height : ℕ} where

open import Data.Bool as Bool using (Bool; true; false; if_then_else_; not; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Integer as ℤ using (ℤ; 0ℤ; _+_; _-_; _*_; +_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷⁺_; head) renaming (_∷_ to _⁺∷_)
open import Data.List.Relation.Unary.Linked using (Linked; [-]) renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec as Vec using (Vec; _[_]≔_)
open import Function using (_$_; _∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (_because_; ofʸ)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Player
open import Point
open import Pos renaming (Pos to FinPos)

Pos : Set
Pos = FinPos width height

open import Data.Tree.AVL (Pos-strictTotalOrder {width} {height}) as AVL using ()
open import Data.Tree.AVL.Sets (Pos-strictTotalOrder {width} {height}) as S renaming (⟨Set⟩ to ⟨Set⟩ₚₒₛ)

IsChain : List Pos → Set
IsChain = Linked Adjacent

IsChain⁺ : List⁺ Pos → Set
IsChain⁺ = IsChain ∘ List⁺.toList

data IsRing : List Pos → Set where
  ring-init : ∀ {pos₁ pos₂ : Pos} → Adjacent pos₁ pos₂ → IsRing (pos₁ ∷ pos₂ ∷ [])
  ring-extend : ∀ {pos₁ pos₂ : Pos} {list : List Pos} → IsRing (pos₁ ∷ list) → IsRing (pos₁ ∷ pos₂ ∷ list)

IsRing⁺ : List⁺ Pos → Set
IsRing⁺ = IsRing ∘ List⁺.toList

SameHead : {A : Set} → List⁺ A → List⁺ A → Set
SameHead a b = head a ≡ head b

data SameLast {A : Set} : List⁺ A → List⁺ A → Set where
  [-]ₛₗ : ∀ {a : A} → SameLast (a ⁺∷ []) (a ⁺∷ [])
  _∷ₛₗₗ_ : ∀ {l₁ l₂ : List⁺ A} (a : A) → SameLast l₁ l₂ → SameLast (a ∷⁺ l₁) l₂
  _∷ₛₗᵣ_ : ∀ {l₁ l₂ : List⁺ A} (a : A) → SameLast l₁ l₂ → SameLast l₁ (a ∷⁺ l₂)

same-last-lemm₁ : ∀ {A : Set} {l : List A} {a : A} → SameLast (a ⁺∷ l) (a ⁺∷ l)
same-last-lemm₁ {l = []} = [-]ₛₗ
same-last-lemm₁ {l = _ ∷ l} {a = a} = a ∷ₛₗₗ (a ∷ₛₗᵣ same-last-lemm₁)

same-last-lemm₂ : ∀ {A : Set} {l₁ l₂ : List⁺ A} → SameLast l₁ l₂ → SameLast l₂ l₁
same-last-lemm₂ [-]ₛₗ = [-]ₛₗ
same-last-lemm₂ (a ∷ₛₗₗ sameLast) = a ∷ₛₗᵣ same-last-lemm₂ sameLast
same-last-lemm₂ (a ∷ₛₗᵣ sameLast) = a ∷ₛₗₗ same-last-lemm₂ sameLast

same-last-lemm₃ : ∀ {A : Set} {a : A} {l₁ l₂ : List⁺ A} → SameLast (a ∷⁺ l₁) l₂ → SameLast l₁ l₂
same-last-lemm₃ (_ ∷ₛₗₗ sameLast) = sameLast
same-last-lemm₃ (a ∷ₛₗᵣ sameLast) = a ∷ₛₗᵣ same-last-lemm₃ sameLast

same-last-lemm₄ : ∀ {A : Set} {l₁ l₂ l₃ : List⁺ A} → SameLast l₁ l₂ → SameLast l₂ l₃ → SameLast l₁ l₃
same-last-lemm₄ [-]ₛₗ b = b
same-last-lemm₄ (x ∷ₛₗₗ a) b = x ∷ₛₗₗ same-last-lemm₄ a b
same-last-lemm₄ (x ∷ₛₗᵣ a) (.x ∷ₛₗₗ b) = same-last-lemm₄ a b
same-last-lemm₄ {l₂ = .x ⁺∷ z ∷ l₂} (x ∷ₛₗᵣ a) (y ∷ₛₗᵣ b) = y ∷ₛₗᵣ same-last-lemm₄ a (same-last-lemm₃ b)

is-ring-lemm : ∀ {ring₁ ring₂ : List⁺ Pos} → IsRing⁺ ring₁ → SameHead ring₁ ring₂ → SameLast ring₁ ring₂ → IsRing⁺ ring₂
is-ring-lemm {.pos₁ ⁺∷ .pos₁ ∷ []} {pos₁ ⁺∷ []} (ring-init adj) refl (.pos₁ ∷ₛₗₗ [-]ₛₗ) =  ⊥-elim (adjacent-⊥ adj)
is-ring-lemm {.pos₁ ⁺∷ pos₂ ∷ []} {pos₁ ⁺∷ .pos₂ ∷ []} (ring-init adj) refl (.pos₁ ∷ₛₗₗ (.pos₁ ∷ₛₗᵣ [-]ₛₗ)) = ring-init adj
is-ring-lemm {.pos₁ ⁺∷ pos₂ ∷ []} {pos₁ ⁺∷ .pos₂ ∷ []} (ring-init adj) refl (.pos₁ ∷ₛₗᵣ (.pos₁ ∷ₛₗₗ [-]ₛₗ)) = ring-init adj
is-ring-lemm {.pos ⁺∷ _ ∷ []} {pos ⁺∷ _ ∷ _ ∷ tail} (ring-init adj) refl sameLast = ring-extend (is-ring-lemm (ring-init adj) refl $
  same-last-lemm₂ (pos ∷ₛₗₗ same-last-lemm₃ (same-last-lemm₃ (same-last-lemm₂ sameLast))))
is-ring-lemm {.pos ⁺∷ _ ∷ _ ∷ ring₁} {pos ⁺∷ ring₂} (ring-extend isRing) refl sameLast = is-ring-lemm isRing refl (pos ∷ₛₗₗ same-last-lemm₃ (same-last-lemm₃ sameLast))

record Field : Set where
  field
    scoreRed scoreBlack : ℕ
    moves : List (Pos × Player)
    lastSurroundChains : List (∃[ chain ] (IsChain⁺ chain × IsRing⁺ chain))
    lastSurroundPlayer : Player
    points : Vec Point (width ℕ.* height)

point : Field → Pos → Point
point record { points = points } = Vec.lookup points ∘ Pos.toFin

isPuttingAllowed : Field → Pos → Bool
isPuttingAllowed fld pos with point fld pos
... | EmptyPoint = true
... | EmptyBasePoint _ = true
... | _ = false

isPlayer : Field → Pos → Player → Bool
isPlayer fld pos player with point fld pos
... | PlayerPoint p = ⌊ p ≟ₚₗ player ⌋
... | BasePoint p _ = ⌊ p ≟ₚₗ player ⌋
... | _ = false

isPlayersPoint : Field → Pos → Player → Bool
isPlayersPoint fld pos player = ⌊ point fld pos ≟ₚₜ PlayerPoint player ⌋

isCapturedPoint : Field → Pos → Player → Bool
isCapturedPoint fld pos player = ⌊ point fld pos ≟ₚₜ BasePoint (next player) true ⌋

isEmptyBase : Field → Pos → Player → Bool
isEmptyBase fld pos player = ⌊ point fld pos ≟ₚₜ EmptyBasePoint player ⌋

emptyField : Field
emptyField = record { scoreRed = 0
                    ; scoreBlack = 0
                    ; moves = []
                    ; lastSurroundChains = []
                    ; lastSurroundPlayer = Red
                    ; points = Vec.replicate _ EmptyPoint
                    }

{-# TERMINATING #-}
wave : Pos → (Pos → Bool) → ⟨Set⟩ₚₒₛ
wave startPos f = wave' S.empty (S.singleton startPos)
  where _\\ₛ_ : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        _\\ₛ_ set₁ set₂ = List.foldr S.delete set₁ (S.toList set₂)
        neighborhood : Pos → List Pos
        neighborhood pos = List.mapMaybe (Maybe.map proj₁) $ n‵ pos
                                                           ∷ s‵ pos
                                                           ∷ w‵ pos
                                                           ∷ e‵ pos
                                                           ∷ []
        nextFront : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        nextFront passed front = (S.fromList $ List.filter ((Bool._≟ true) ∘ f) $ List.concatMap neighborhood (S.toList front)) \\ₛ passed
        wave' : ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ → ⟨Set⟩ₚₒₛ
        wave' passed front = if List.null (S.toList front)
                             then passed
                             else wave' (AVL.union passed front) (nextFront passed front)

getInputPoints : Field → (pos : Pos) → Player → List ((∃[ chainPos ] Adjacent pos chainPos) × (∃[ capturedPos ] Adjacent pos capturedPos))
getInputPoints fld pos player =
  let isDirectionPlayer : ((pos₁ : Pos) → Maybe (∃[ pos₂ ] Adjacent pos₁ pos₂)) → Bool
      isDirectionPlayer dir = Maybe.maybe′ (λ{(dirPos , _) → isPlayer fld dirPos player}) false $ dir pos
      list₁ = if not $ isDirectionPlayer w‵ then
                if isDirectionPlayer nw‵ then List.fromMaybe (Maybe.zip (nw‵ pos) (w‵ pos))
                else if isDirectionPlayer n‵ then List.fromMaybe (Maybe.zip (n‵ pos) (w‵ pos))
                else []
              else
                []
      list₂ = if not $ isDirectionPlayer s‵ then
                if isDirectionPlayer sw‵ then List.fromMaybe (Maybe.zip (sw‵ pos) (s‵ pos)) ++ list₁
                else if isDirectionPlayer w‵ then List.fromMaybe (Maybe.zip (w‵ pos) (s‵ pos)) ++ list₁
                else list₁
              else
                list₁
      list₃ = if not $ isDirectionPlayer e‵ then
                if isDirectionPlayer se‵ then List.fromMaybe (Maybe.zip (se‵ pos) (e‵ pos)) ++ list₂
                else if isDirectionPlayer s‵ then List.fromMaybe (Maybe.zip (s‵ pos) (e‵ pos)) ++ list₂
                else list₂
              else
                list₂
      list₄ = if not $ isDirectionPlayer n‵ then
                if isDirectionPlayer ne‵ then List.fromMaybe (Maybe.zip (ne‵ pos) (n‵ pos)) ++ list₃
                else if isDirectionPlayer e‵ then List.fromMaybe (Maybe.zip (e‵ pos) (n‵ pos)) ++ list₃
                else list₃
              else
                list₃
  in list₄

square : List Pos → ℤ
square [] = 0ℤ
square (pos ∷ tail) = square‵ $ pos ∷ tail
  where skewProduct : Pos → Pos → ℤ
        skewProduct (x₁ , y₁) (x₂ , y₂) = + toℕ x₁ * + toℕ y₂ - + toℕ y₁ * + toℕ x₂
        square‵ : List Pos → ℤ
        square‵ [] = 0ℤ
        square‵ (pos₁ ∷ []) = skewProduct pos₁ pos
        square‵ (pos₁ ∷ pos₂ ∷ tail) = skewProduct pos₁ pos₂ + square‵ (pos₂ ∷ tail)

-- Removes intersections from a chain.
flatten : (chain₁ : List⁺ Pos) → IsChain⁺ chain₁ → ∃[ chain₂ ] (IsChain⁺ chain₂ × SameHead chain₁ chain₂ × SameLast chain₁ chain₂)
flatten (pos ⁺∷ []) [-] = (pos ⁺∷ [] , ([-] , (refl , [-]ₛₗ)))
flatten (pos₁ ⁺∷ pos₂ ∷ chain) (adj ∷ₗ chainAdj₁) with flatten (pos₂ ⁺∷ chain) chainAdj₁
... | (.pos₂ ⁺∷ chain₂ , (chainAdj₂ , (refl , sameLast))) = (_ , (proj₁ (proj₂ flattened) , (refl , pos₁ ∷ₛₗₗ same-last-lemm₄ sameLast (proj₂ (proj₂ flattened)))))
  where flatten‵ : (chain₁ : List⁺ Pos) → IsChain⁺ chain₁ → Maybe (∃[ chain₂ ] (IsChain⁺ (pos₁ ⁺∷ chain₂) × SameLast chain₁ (pos₁ ⁺∷ chain₂)))
        flatten‵ (pos ⁺∷ []) [-] with pos ≟ₚₒₛ pos₁
        ... | false because _ = nothing
        ... | true because ofʸ refl = just ([] , ([-] , [-]ₛₗ))
        flatten‵ (pos₃ ⁺∷ pos₄ ∷ t) (adj ∷ₗ chainAdj) with pos₃ ≟ₚₒₛ pos₁
        ... | false because _ = Maybe.map (λ{(chain , (isChain , sameLast)) → (chain , (isChain , pos₃ ∷ₛₗₗ sameLast))}) $ flatten‵ (pos₄ ⁺∷ t) chainAdj
        ... | true because ofʸ refl = just (pos₄ ∷ t , (adj ∷ₗ chainAdj , pos₃ ∷ₛₗₗ (pos₃ ∷ₛₗᵣ same-last-lemm₁)))
        flattened = Maybe.fromMaybe (pos₂ ∷ chain , (adj ∷ₗ chainAdj₁ , pos₁ ∷ₛₗᵣ same-last-lemm₂ sameLast)) $ flatten‵ (pos₂ ⁺∷ chain₂) chainAdj₂

{-# TERMINATING #-}
buildChain : Field → (startPos nextPos : Pos) → Adjacent startPos nextPos → Player → Maybe (∃[ chain ] (IsChain⁺ chain × IsRing⁺ chain))
buildChain fld startPos nextPos adj player = if ⌊ square (List⁺.toList (proj₁ chain₂)) ℤ.<? 0ℤ ⌋ then just chain₂ else nothing
  where getNextPlayerPos : (pos₁ : Pos) → Direction → ∃[ pos₂ ] Adjacent pos₁ pos₂
        getNextPlayerPos centerPos dir with direction→pos dir centerPos
        ... | nothing = getNextPlayerPos centerPos $ rotate dir -- TODO: use filter + maybe′ ?
        ... | just (pos , adj) = if ⌊ pos ≟ₚₒₛ startPos ⌋ ∨ (isPlayer fld pos player) then (pos , adj)
                                 else (getNextPlayerPos centerPos $ rotate dir)
        getChain : (startPos‵ nextPos‵ : Pos) → Adjacent startPos‵ nextPos‵ → ∃[ chain ] (IsChain⁺ (startPos‵ ∷⁺ chain) × IsRing⁺ (startPos ∷⁺ chain))
        getChain _ nextPos adj = let (nextPos‵ , nextAdj) = getNextPlayerPos nextPos (rotate¬adjacent (inverse (direction adj)))
                                     (nextChain , (nextChainAdj , nextRing)) = getChain nextPos nextPos‵ nextAdj
                                 in case nextPos‵ ≟ₚₒₛ startPos of
                                    λ { (true because ofʸ proof) → (nextPos ⁺∷ [] , (adj ∷ₗ [-] , ring-init (adjacent-symm (subst (Adjacent nextPos) proof nextAdj))))
                                      ; (false because _) → (nextPos ∷⁺ nextChain , (adj ∷ₗ nextChainAdj , ring-extend nextRing))
                                      }
        chain₁ : ∃[ chain ] (IsChain⁺ (startPos ∷⁺ chain) × IsRing⁺ (startPos ∷⁺ chain))
        chain₁ = (_ , proj₂ (getChain startPos nextPos adj))
        chain₂ : ∃[ chain ] (IsChain⁺ chain × IsRing⁺ chain)
        chain₂ = map₂ (λ{(isChain , (refl , sameLast)) → (isChain , is-ring-lemm (proj₂ (proj₂ chain₁)) refl sameLast) }) $ flatten (startPos ∷⁺ proj₁ chain₁) (proj₁ (proj₂ chain₁))

posInsideRing : Pos → List Pos → Bool
posInsideRing pos ring = intersectionsCount ring $ firstIntersectionState $ List.reverse ring
  where open import Data.Fin.Properties using (_≤?_)
        open import Data.Fin.Patterns
        open import Data.Fin using (suc)
        data IntersectionState : Set where
          is↑ : IntersectionState
          is↔ : IntersectionState
          is↓ : IntersectionState
          is× : IntersectionState
        intersectionState : Pos → Pos → IntersectionState
        intersectionState (x₁ , y₁) (x₂ , y₂) = if ⌊ x₁ ≤? x₂ ⌋ then intersectionState‵ y₁ y₂ else is×
          where intersectionState‵ : ∀ {n} → Fin n → Fin n → IntersectionState
                intersectionState‵ 0F 0F = is↔
                intersectionState‵ 1F 0F = is↑
                intersectionState‵ 0F 1F = is↓
                intersectionState‵ 0F (suc (suc _)) = is×
                intersectionState‵ (suc (suc _)) 0F = is×
                intersectionState‵ (suc y₁) (suc y₂) = intersectionState‵ y₁ y₂
        firstIntersectionState : List Pos → IntersectionState
        firstIntersectionState [] = is×
        firstIntersectionState (pos₂ ∷ tail) with intersectionState pos pos₂
        ... | is↔ = firstIntersectionState tail
        ... | is = is
        intersectionsCount : List Pos → IntersectionState → Bool
        intersectionsCount [] _ = false
        intersectionsCount (pos₂ ∷ tail) is with intersectionState pos pos₂
        intersectionsCount (_ ∷ tail) is↓ | is↑ = not $ intersectionsCount tail is↑
        intersectionsCount (_ ∷ tail) is↑ | is↓ = not $ intersectionsCount tail is↓
        intersectionsCount (_ ∷ tail) is | is↔ = intersectionsCount tail is
        intersectionsCount (_ ∷ tail) _ | is = intersectionsCount tail is

getInsideRing : Pos → List Pos -> ⟨Set⟩ₚₒₛ
getInsideRing startPos ring =
  let ringSet = S.fromList ring
  in wave startPos (not ∘ (S._∈? ringSet))

{-# TERMINATING #-}
getEmptyBaseChain : Field → Pos -> Player → Maybe (∃[ chain ] (IsChain⁺ chain × IsRing⁺ chain))
getEmptyBaseChain fld startPos player = (w startPos) Maybe.>>= (getEmptyBaseChain‵ ∘ proj₁)
  where getEmptyBaseChain‵ : Pos → Maybe (∃[ chain ] (IsChain⁺ chain × IsRing⁺ chain))
        getEmptyBaseChain‵ pos = if not $ isPlayer fld pos player then (w pos) Maybe.>>= (getEmptyBaseChain‵ ∘ proj₁)
                                 else let inputPoints = getInputPoints fld pos player
                                          chains = List.mapMaybe (λ{((chainPos , adj) , _) -> buildChain fld pos chainPos adj player}) inputPoints
                                          result = List.head $ List.filter ((Bool._≟ true) ∘ posInsideRing startPos ∘ List⁺.toList ∘ proj₁) chains
                                      in result Maybe.<∣> ((w pos) Maybe.>>= (getEmptyBaseChain‵ ∘ proj₁))

capture : Player → Point → Point
capture player EmptyPoint = BasePoint player false
capture player (PlayerPoint player‵) = if ⌊ player‵ ≟ₚₗ player ⌋
                                       then PlayerPoint player‵
                                       else BasePoint player true
capture player (BasePoint player‵ enemy) = if ⌊ player‵ ≟ₚₗ player ⌋
                                           then BasePoint player‵ enemy
                                           else (if enemy
                                                 then PlayerPoint player
                                                 else BasePoint player false)
capture player (EmptyBasePoint _) = BasePoint player false

putPoint : (pos : Pos) → Player → (fld : Field) → Bool.T (isPuttingAllowed fld pos) → Field
putPoint pos player fld _ =
  let enemyPlayer = next player
      enemyEmptyBaseChain = getEmptyBaseChain fld pos enemyPlayer
      enemyEmptyBase = List.filter (λ pos‵ → isEmptyBase fld pos‵ enemyPlayer Bool.≟ true) $
                       S.toList $
                       Maybe.maybe′ (λ{(chain , _) → getInsideRing pos (List⁺.toList chain)}) S.empty enemyEmptyBaseChain
      inputPoints = getInputPoints fld pos player
      captures = List.mapMaybe (λ{((chainPos , chainAdj) , (capturedPos , _)) →
        Maybe.map (λ chain →
          (chain , (S.toList $ getInsideRing capturedPos $ List⁺.toList $ proj₁ chain))) (buildChain fld pos chainPos chainAdj player)}) inputPoints
      capturedCount = List.length ∘ List.filter (λ pos‵ → isPlayersPoint fld pos‵ enemyPlayer Bool.≟ true)
      freedCount = List.length ∘ List.filter (λ pos‵ → isCapturedPoint fld pos‵ player Bool.≟ true)
      (emptyCaptures , realCaptures) = List.partition (λ{(_ , captured) → capturedCount captured ℕ.≟ 0}) captures
      capturedTotal = List.sum $ List.map (capturedCount ∘ proj₂) realCaptures
      freedTotal = List.sum $ List.map (freedCount ∘ proj₂) realCaptures
      newEmptyBase = S.fromList $ List.filter (λ pos‵ → point fld pos‵ ≟ₚₜ EmptyPoint) $ List.concatMap proj₂ emptyCaptures
      realCaptured = List.concatMap proj₂ realCaptures
      newScoreRed = if ⌊ player ≟ₚₗ Red ⌋ then Field.scoreRed fld ℕ.+ capturedTotal else Field.scoreRed fld ℕ.∸ freedTotal
      newScoreBlack = if ⌊ player ≟ₚₗ Black ⌋ then Field.scoreBlack fld ℕ.+ capturedTotal else Field.scoreBlack fld ℕ.∸ freedTotal
      newMoves = (pos , player) ∷ Field.moves fld
      point‵ = point fld pos
  in if ⌊ point‵ ≟ₚₜ EmptyBasePoint enemyPlayer ⌋
     then if not $ List.null captures
          then record
               { scoreRed = newScoreRed
               ; scoreBlack = newScoreBlack
               ; moves = newMoves
               ; lastSurroundChains = List.map proj₁ realCaptures
               ; lastSurroundPlayer = player
               ; points = let points₁ = Field.points fld [ Pos.toFin pos ]≔ PlayerPoint player
                              points₂ = List.foldr (λ pos‵ points → points [ Pos.toFin pos‵ ]≔ EmptyPoint) points₁ enemyEmptyBase
                              points₃ = List.foldr (λ pos‵ points → points [ Pos.toFin pos‵ ]≔ capture player (point fld pos‵)) points₂ realCaptured
                          in points₃
               }
          else record
               { scoreRed = if ⌊ player ≟ₚₗ Red ⌋ then Field.scoreRed fld else Field.scoreRed fld ℕ.+ 1
               ; scoreBlack = if ⌊ player ≟ₚₗ Black ⌋ then Field.scoreBlack fld else Field.scoreBlack fld ℕ.+ 1
               ; moves = newMoves
               ; lastSurroundChains = List.fromMaybe enemyEmptyBaseChain
               ; lastSurroundPlayer = enemyPlayer
               ; points = let points₁ = List.foldr (λ pos‵ points → points [ Pos.toFin pos‵ ]≔ BasePoint enemyPlayer false) (Field.points fld) enemyEmptyBase
                              points₂ = points₁ [ Pos.toFin pos ]≔ BasePoint enemyPlayer true
                          in points₂
               }
     else if ⌊ point‵ ≟ₚₜ EmptyBasePoint player ⌋
     then record
          { Field fld
          ; moves = newMoves
          ; lastSurroundChains = []
          ; lastSurroundPlayer = player
          ; points = Field.points fld [ Pos.toFin pos ]≔ PlayerPoint player
          }
     else record
          { scoreRed = newScoreRed
          ; scoreBlack = newScoreBlack
          ; moves = newMoves
          ; lastSurroundChains = List.map proj₁ realCaptures
          ; lastSurroundPlayer = player
          ; points = let points₁ = Field.points fld [ Pos.toFin pos ]≔ PlayerPoint player
                         points₂ = S.foldr (λ pos‵ points → points [ Pos.toFin pos‵ ]≔ EmptyBasePoint player) points₁ newEmptyBase
                         points₃ = List.foldr (λ pos‵ points → points [ Pos.toFin pos‵ ]≔ capture player (point fld pos‵)) points₂ realCaptured
                     in points₃
          }

lastPlayer : Field → Maybe Player
lastPlayer = Maybe.map proj₂ ∘ List.head ∘ Field.moves

nextPlayer : Field → Player
nextPlayer = Maybe.fromMaybe Player.Red ∘ Maybe.map Player.next ∘ lastPlayer

putNextPoint : (pos : Pos) → (fld : Field) → Bool.T (isPuttingAllowed fld pos) → Field
putNextPoint pos fld = putPoint pos (nextPlayer fld) fld

winner : Field → Maybe Player
winner fld =
  if ⌊ Field.scoreBlack fld ℕ.<? Field.scoreRed fld ⌋
  then just Player.Red
  else if ⌊ Field.scoreRed fld ℕ.<? Field.scoreBlack fld ⌋
  then just Player.Black
  else nothing
