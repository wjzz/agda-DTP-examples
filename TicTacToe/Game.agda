-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-07-11
-- @tags   : agda ; tic-tac-toe
-- @short  : A safe implementation of the TicTacToe game in Agda

module Game where

-- computational parts

open import Data.Bool
open import Data.List      hiding (partition)
open import Data.Maybe
open import Data.Nat       renaming ( _≟_ to _≟ℕ_
                                    ; _⊔_ to max
                                    )
open import Data.Product
open import Data.Sum
open import Data.Vec       renaming ( map to vmap)
open import Data.Vec.Utils renaming ( map-in to vmap-in 
                                    ; delete to vdelete
                                    ; _⊂_ to _⊂-v_
                                    )

-- propositional parts

open import Data.Empty
open import NatUtils
open import ListUtils renaming ( _∈_ to _∈-list_
                               ; _∉_ to _∉-list_
                               )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

{- BASE IMPORT Data.Nat.Theorems  -}

--------------------
-- the color type
--------------------

data Color : Set where
  X O : Color

otherColor : Color → Color
otherColor X = O
otherColor O = X

otherColorValid : ∀ (c : Color) → otherColor c ≢ c
otherColorValid X ()
otherColorValid O ()

-------------------
-- the move type
-------------------

data Move : Set where
  P11 P12 P13 : Move
  P21 P22 P23 : Move
  P31 P32 P33 : Move


-- a list of all possible moves

allMoves : Vec Move 9
allMoves = P11 ∷ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ []

allMovesValid : ∀ (m : Move) → m ∈ allMoves
allMovesValid P11 = here
allMovesValid P12 = there here
allMovesValid P13 = there (there here)
allMovesValid P21 = there (there (there here))
allMovesValid P22 = there (there (there (there here)))
allMovesValid P23 = there (there (there (there (there here))))
allMovesValid P31 = there (there (there (there (there (there here)))))
allMovesValid P32 = there (there (there (there (there (there (there here))))))
allMovesValid P33 = there (there (there (there (there (there (there (there here)))))))

-- decidable equality on moves

_==_ : (m1 m2 : Move) → Dec (m1 ≡ m2)
P11 == P11 = yes refl
P11 == P12 = no (λ ())
P11 == P13 = no (λ ())
P11 == P21 = no (λ ())
P11 == P22 = no (λ ())
P11 == P23 = no (λ ())
P11 == P31 = no (λ ())
P11 == P32 = no (λ ())
P11 == P33 = no (λ ())
P12 == P11 = no (λ ())
P12 == P12 = yes refl
P12 == P13 = no (λ ())
P12 == P21 = no (λ ())
P12 == P22 = no (λ ())
P12 == P23 = no (λ ())
P12 == P31 = no (λ ())
P12 == P32 = no (λ ())
P12 == P33 = no (λ ())
P13 == P11 = no (λ ())
P13 == P12 = no (λ ())
P13 == P13 = yes refl
P13 == P21 = no (λ ())
P13 == P22 = no (λ ())
P13 == P23 = no (λ ())
P13 == P31 = no (λ ())
P13 == P32 = no (λ ())
P13 == P33 = no (λ ())
P21 == P11 = no (λ ())
P21 == P12 = no (λ ())
P21 == P13 = no (λ ())
P21 == P21 = yes refl
P21 == P22 = no (λ ())
P21 == P23 = no (λ ())
P21 == P31 = no (λ ())
P21 == P32 = no (λ ())
P21 == P33 = no (λ ())
P22 == P11 = no (λ ())
P22 == P12 = no (λ ())
P22 == P13 = no (λ ())
P22 == P21 = no (λ ())
P22 == P22 = yes refl
P22 == P23 = no (λ ())
P22 == P31 = no (λ ())
P22 == P32 = no (λ ())
P22 == P33 = no (λ ())
P23 == P11 = no (λ ())
P23 == P12 = no (λ ())
P23 == P13 = no (λ ())
P23 == P21 = no (λ ())
P23 == P22 = no (λ ())
P23 == P23 = yes refl
P23 == P31 = no (λ ())
P23 == P32 = no (λ ())
P23 == P33 = no (λ ())
P31 == P11 = no (λ ())
P31 == P12 = no (λ ())
P31 == P13 = no (λ ())
P31 == P21 = no (λ ())
P31 == P22 = no (λ ())
P31 == P23 = no (λ ())
P31 == P31 = yes refl
P31 == P32 = no (λ ())
P31 == P33 = no (λ ())
P32 == P11 = no (λ ())
P32 == P12 = no (λ ())
P32 == P13 = no (λ ())
P32 == P21 = no (λ ())
P32 == P22 = no (λ ())
P32 == P23 = no (λ ())
P32 == P31 = no (λ ())
P32 == P32 = yes refl
P32 == P33 = no (λ ())
P33 == P11 = no (λ ())
P33 == P12 = no (λ ())
P33 == P13 = no (λ ())
P33 == P21 = no (λ ())
P33 == P22 = no (λ ())
P33 == P23 = no (λ ())
P33 == P31 = no (λ ())
P33 == P32 = no (λ ())
P33 == P33 = yes refl


------------------------
--  The result type   --
------------------------

data Result : Set where
  Win  : (c : Color) → Result
  Draw : Result


-----------------------------------------------------------------------------------------------------------------
--  An implementation of the TicTacToe game system that will reify the API and provide many static guarantees  --
-----------------------------------------------------------------------------------------------------------------

module GameImplementation where
  --private

  -----------------------------------------------------------------
  -- the moves type
  --
  -- A list of moves augmented with the color of the player to move 
  -- and the number of moves already played
  -----------------------------------------------------------------

  infixr 5 _∷_

  data Moves : (currPlayer : Color) → (n : ℕ) → Set where
    []  : Moves X 0
    _∷_ : {c : Color} {n : ℕ} → (m : Move) → (ms : Moves c n) → Moves (otherColor c) (suc n)
  
  -- moves membership relation

  infix 4 _∈'_

  data _∈'_ : {c : Color} {n : ℕ} → Move → Moves c n → Set where
    here    : {c : Color} {n : ℕ} {m    : Move} {ms : Moves c n} → m ∈' m ∷ ms
    there   : {c : Color} {n : ℕ} {m m' : Move} {ms : Moves c n} → m ∈' ms → m ∈' m' ∷ ms
  
  infix 4 _∉'_

  _∉'_ : {c : Color} {n : ℕ} → Move → Moves c n → Set
  _∉'_ m ms = ¬ (m ∈' ms)


  -- move membership is decidable

  lem-∈'-neq : ∀ {c : Color}{n : ℕ} → (m1 m2 : Move) → (ms : Moves c n) → m1 ≢ m2 → ¬ (m1 ∈' ms) → ¬ (m1 ∈' m2 ∷ ms)
  lem-∈'-neq .m2 m2 ms neq nin here = neq refl
  lem-∈'-neq m1 m2 ms neq nin (there y) = nin y

  member′ : {c : Color}{n : ℕ} → (m : Move) → (ms : Moves c n) → Dec (m ∈' ms)
  member′ m [] = no (λ ())
  member′ m (m' ∷ ms) with m == m'
  ... | yes p rewrite p = yes here
  ... | no ¬p with member′ m ms
  ... | yes p' = yes (there p')
  ... | no ¬p' = no (lem-∈'-neq m m' ms ¬p ¬p')


  -- selectors by color
  -- TODO: should we change the result type to Vec Move (something-related-to n/2)?

  xMoves : {c : Color} {n : ℕ} → Moves c n → List Move
  xMoves []             = []
  xMoves (_∷_ {X} m ms) = m ∷ xMoves ms
  xMoves (_∷_ {O} m ms) = xMoves ms
  
  oMoves : {c : Color} {n : ℕ} → Moves c n → List Move
  oMoves []             = []
  oMoves (_∷_ {X} m ms) = oMoves ms
  oMoves (_∷_ {O} m ms) = m ∷ oMoves ms
  
  -- we can write a version with a more precise type, but unfortunately
  -- the definitions become more complicated 
  -- (however, this way we don't need to write any proofs! 
  --   [because the structure is exactly the same ;-) ])

  colorwiseHalf : (c : Color) → (n : ℕ) → ℕ
  colorwiseHalf c zero          = 0
  colorwiseHalf X (suc zero)    = 1
  colorwiseHalf O (suc zero)    = 0
  colorwiseHalf c (suc (suc n)) = 1 + colorwiseHalf c n

  xMovesVec : {c : Color} {n : ℕ} → Moves c n → Vec Move (colorwiseHalf X n)
  xMovesVec []                         = []
  xMovesVec (m ∷ [])                   = m ∷ []
  xMovesVec {.O} (m ∷ (_∷_ {O} m' ms)) = m  ∷ xMovesVec ms
  xMovesVec {.X} (m ∷ (_∷_ {X} m' ms)) = m' ∷ xMovesVec ms

  oMovesVec : {c : Color} {n : ℕ} → Moves c n → Vec Move (colorwiseHalf O n)
  oMovesVec []                         = []
  oMovesVec (m ∷ [])                   = []
  oMovesVec {.O} (m ∷ (_∷_ {O} m' ms)) = m' ∷ oMovesVec ms
  oMovesVec {.X} (m ∷ (_∷_ {X} m' ms)) = m  ∷ oMovesVec ms

  movesByColor : forall {c0 n} → (c : Color) → (m : Moves c0 n) → List Move
  movesByColor X m = xMoves m
  movesByColor O m = oMoves m

  movesByColorVec : forall {c0 n} → (c : Color) → (m : Moves c0 n) → Vec Move (colorwiseHalf c n)
  movesByColorVec X m = xMovesVec m
  movesByColorVec O m = oMovesVec m

  lem-same-color : ∀ {n} (cand : Color) → (m : Move) (ms : Moves (otherColor cand) n) → movesByColor cand ms ≡ movesByColor cand (m ∷ ms)
  lem-same-color X m ms = refl
  lem-same-color O m ms = refl

  lem-other-color : ∀ {n} (cand : Color) → (m : Move) (ms : Moves cand n) → m ∷ movesByColor cand ms ≡ movesByColor cand (m ∷ ms)
  lem-other-color X m ms = refl
  lem-other-color O m ms = refl

  lem-movesByColor-ext : ∀ {c n} (cand : Color) → (m : Move) (ms : Moves c n) → movesByColor cand ms ⊂ movesByColor cand (m ∷ ms)
  lem-movesByColor-ext {X} X m ms = lem-⊂-ext m (xMoves ms) (xMoves ms) (⊂-refl (xMoves ms))
  lem-movesByColor-ext {O} X m ms = ⊂-refl (xMoves ms)
  lem-movesByColor-ext {X} O m ms = ⊂-refl (oMoves ms)
  lem-movesByColor-ext {O} O m ms = lem-⊂-ext m (oMoves ms) (oMoves ms) (⊂-refl (oMoves ms))

  -------------------------
  --  winning positions  --
  -------------------------

  -- winning configurations

  winningPositions : List (List Move)
  winningPositions = (P11 ∷ P12 ∷ P13 ∷ []) ∷                        -- horizontal 
                     (P21 ∷ P22 ∷ P23 ∷ []) ∷ 
                     (P31 ∷ P32 ∷ P33 ∷ []) ∷ 
                   
                     (P11 ∷ P21 ∷ P31 ∷ []) ∷                        -- vertical
                     (P12 ∷ P22 ∷ P32 ∷ []) ∷ 
                     (P13 ∷ P23 ∷ P33 ∷ []) ∷ 

                     (P11 ∷ P22 ∷ P33 ∷ []) ∷                        -- diagonal
                     (P13 ∷ P22 ∷ P31 ∷ []) ∷ 
                     []


  winningPositionsVec : Vec (Vec Move 3) _        -- using underscores can help if we change that one day
  winningPositionsVec = (P11 ∷ P12 ∷ P13 ∷ []) ∷                        -- horizontal 
                        (P21 ∷ P22 ∷ P23 ∷ []) ∷ 
                        (P31 ∷ P32 ∷ P33 ∷ []) ∷ 
                   
                        (P11 ∷ P21 ∷ P31 ∷ []) ∷                        -- vertical
                        (P12 ∷ P22 ∷ P32 ∷ []) ∷ 
                        (P13 ∷ P23 ∷ P33 ∷ []) ∷ 

                        (P11 ∷ P22 ∷ P33 ∷ []) ∷                        -- diagonal
                        (P13 ∷ P22 ∷ P31 ∷ []) ∷ 
                        []

  -- the won relation for the Moves type

  data WonC : forall {c n} → (winner : Color) (ms : Moves c n) → Set where
    wonC : ∀ {c n winner} → (m : Moves c n) → (winning : List Move) →
             winning ∈-list winningPositions → 
             winning ⊂ movesByColor winner m →
             WonC winner m              
  
  noWinner : forall {c n} → Moves c n → Set
  noWinner b = (¬ WonC X b) × (¬ WonC O b)

  -- basic properties 
                                        
  lem-won-empty : ∀ (c : Color) → ¬ WonC c []
  lem-won-empty c (wonC .[] .[] (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ())))))))) nil)
  lem-won-empty X (wonC .[] .(m ∷ ms) y (cons {m} {ms} y' ()))
  lem-won-empty O (wonC .[] .(m ∷ ms) y (cons {m} {ms} y' ()))

  lem-win-extend : ∀ {c n} → (winner : Color) (ms : Moves c n) → (m : Move) → WonC winner ms → WonC winner (m ∷ ms)
  lem-win-extend winner ms m (wonC .ms winning winningPosition winnning∈movesByClr) 
    = wonC (m ∷ ms) winning winningPosition (⊂-trans winnning∈movesByClr (lem-movesByColor-ext winner m ms))

  lem-nowin-prev : ∀ {c n} → (winner : Color)(ms : Moves c n) → (m : Move) → ¬ WonC winner (m ∷ ms) → ¬ WonC winner ms
  lem-nowin-prev winner ms m x x' = x (lem-win-extend winner ms m x')
    
  -- You couldn't have just won if it wasn't your turn to play!
  -- At least in tic-tac-toe...

  lem-other-player-cant-win : ∀ {c n} → (ms : Moves c n) → (m : Move) → ¬ WonC (otherColor c) ms → ¬ WonC (otherColor c) (m ∷ ms)
  lem-other-player-cant-win {X} ms m ¬Won-ms (wonC .(m ∷ ms) winning winning∈winPos win⊂byColor) = ¬Won-ms (wonC ms winning winning∈winPos win⊂byColor)
  lem-other-player-cant-win {O} ms m ¬Won-ms (wonC .(m ∷ ms) winning winning∈winPos win⊂byColor) = ¬Won-ms (wonC ms winning winning∈winPos win⊂byColor)

  {- BASE won lem-won-empty lem-nowin-prev lem-win-extend -}


  P : forall {c n} → Color → Moves c n → List Move → Set
  P cand ms winConfig = winConfig ⊂ movesByColor cand ms

  decP : forall {c n} → (cand : Color) → (ms : Moves c n) → (x : List Move) → Dec (x ⊂ movesByColor cand ms)
  decP cand ms l = subsetDec l (movesByColor cand ms) _==_

  wonDec : forall {c n} → (cand : Color) → (ms : Moves c n) → Dec (WonC cand ms)
  wonDec cand ms with any-dec (P cand ms) winningPositions (decP cand ms)
  wonDec cand ms | yes p with lem-any-exists (P cand ms) winningPositions p
  ... | winningPosition , inWinning , movesSubset = yes (wonC ms winningPosition inWinning movesSubset)
  wonDec cand ms | no ¬p with lem-none-exists (P cand ms) winningPositions ¬p
  ... | noWinningPosition = no lem where
    lem : (x : WonC cand ms) → ⊥
    lem (wonC .ms winning y y') = noWinningPosition (winning , y , y')


  ----------------------------------------------
  --  A view for checking the current status  --
  ----------------------------------------------

  data GameStatus : ∀ {c n} → Moves c n → Set where

    stWon        : ∀ {c n} {ms : Moves c n} {m : Move}                  
                 →   WonC c              (m ∷ ms)
                 → ¬ WonC (otherColor c) (m ∷ ms)
                 → GameStatus (m ∷ ms)

    stDraw       : ∀ {c n} {ms : Moves c n} {m : Move}                    
                 → noWinner (m ∷ ms)
                 → n ≡ 8
                 → GameStatus (m ∷ ms)

    stInProgress : ∀ {c n} {ms : Moves c n} {m : Move}                    
                 → noWinner (m ∷ ms)
                 → n ≢ 8
                 → GameStatus (m ∷ ms)

  checkGameStatus : ∀ {c n} (ms : Moves c n) (m : Move) → noWinner ms → n < 9 → GameStatus (m ∷ ms)
  checkGameStatus {c} ms m (¬WinX , ¬WinO) n<9 with wonDec c (m ∷ ms)

  -- A) current player has won

  checkGameStatus {X} ms m (¬WinX , ¬WinO) n<9 | yes c-won 
    = stWon c-won (lem-other-player-cant-win ms m ¬WinO)
  checkGameStatus {O} ms m (¬WinX , ¬WinO) n<9 | yes c-won 
    = stWon c-won (lem-other-player-cant-win ms m ¬WinX)

  -- B) current players has not won. Is it a draw?

  checkGameStatus {n = n} ms m (¬WinX , ¬WinO) n<9 | no ¬c-won with n ≟ℕ 8

  -- yes, it's a draw

  checkGameStatus {X} ms m (¬WinX , ¬WinO) n<9 | no ¬c-won | yes n≡8 
    = stDraw (¬c-won , lem-other-player-cant-win ms m ¬WinO) n≡8
  checkGameStatus {O} ms m (¬WinX , ¬WinO) n<9 | no ¬c-won | yes n≡8 
    = stDraw (lem-other-player-cant-win ms m ¬WinX , ¬c-won) n≡8

  -- no, the game continues

  checkGameStatus {X} {n} ms m (¬WinX , ¬WinO) n<9 | no ¬c-won | no ¬n≡8 
    = stInProgress (¬c-won , lem-other-player-cant-win ms m ¬WinO) ¬n≡8
  checkGameStatus {O} {n} ms m (¬WinX , ¬WinO) n<9 | no ¬c-won | no ¬n≡8 
    = stInProgress (lem-other-player-cant-win ms m ¬WinX , ¬c-won) ¬n≡8


  ------------------------------------------------------
  --  A relation that forces every move to be unique  --
  ------------------------------------------------------

  -- a moves list is distinct iff all moves are unique

  data distinct-m : {c : Color} {n : ℕ} → Moves c n → Set where
    dist-nil  : distinct-m []
    dist-cons : {c : Color} {n : ℕ} → {m : Move} {ms : Moves c n} → 
                (v-ms : distinct-m ms) → (m∉ms : m ∉' ms) → distinct-m (m ∷ ms)

  ---------------------------------------------------------------------------------
  --  A relation that states that {made}moves and valid{Moves} form a partition  --
  ---------------------------------------------------------------------------------

  -- TODO: make this into a record

  data partition : {n k : ℕ} {c : Color} → Moves c k → Vec Move n → Set where
    part : {n k : ℕ} {c : Color} 
         → {played   : Moves c k}
         → {possible : Vec Move n}
         → (union    : ∀ (m : Move) → m ∈' played ⊎ m ∈ possible)
         → (inter    : ∀ (m : Move) → m ∈' played → m ∈ possible → ⊥)
         → partition played possible

  ---------------------------------------------------------
  --  A datatype for storing proofs of board invariants  --
  ---------------------------------------------------------

  record invariants {n k : ℕ} {c : Color} (played : Moves c k) (possible : Vec Move n) : Set where
   constructor c-inv
   field
     n+k          : n + k ≡ 9
     k<9          : k < 9
     distPlayed   : distinct-m played
     distPossible : distinct-v possible
     partit       : partition  played possible
     noWin        : noWinner   played

  module I = invariants
  open I

  -------------------------------------------------------------
  --  Preservation of invariants for basic board operations  --
  -------------------------------------------------------------

  ten-nine : ¬ (10 ≤ 9)
  ten-nine (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))

  inv-emptyBoard : {n : ℕ} → (v : Vec Move n) → invariants [] v → ¬ n < 9
  inv-emptyBoard {n} v (c-inv n≡9 y' y0 y1 y2 y3) n<9 rewrite lem-plus-n-0 n | n≡9 = ten-nine n<9

  inv-undoMove : {n k : ℕ} {c : Color} {ms : Moves c k} {possible : Vec Move n} {m : Move} 
               → invariants (m ∷ ms) possible → invariants ms (m ∷ possible)
  inv-undoMove {n} {k} {c} {ms} {possible} {m} 
                (c-inv n+suc-k≡9 1+k<9 (dist-cons v-ms m∉ms) distv 
                (part union inter) noWin) 
                rewrite sym (lem-plus-s n k)
               = c-inv n+suc-k≡9 
                       (lem-<-trans lem-≤-refl 1+k<9) 
                       v-ms 
                       (dist-cons distv (inter m here))
                       (part union2 inter2)
                       (lem-nowin-prev X ms m (proj₁ noWin) , lem-nowin-prev O ms m (proj₂ noWin)) 
                       where
                         union2 : (m' : Move) → m' ∈' ms ⊎ m' ∈ m ∷ possible
                         union2 m2 with union m2
                         union2 .m | inj₁ here      = inj₂ here
                         union2 m2 | inj₁ (there y) = inj₁ y
                         union2 m2 | inj₂ y         = inj₂ (there y)
                       
                         inter2 : (m' : Move) → m' ∈' ms → m' ∈ m ∷ possible → ⊥
                         inter2 .m m2∈ms here         = m∉ms m2∈ms
                         inter2 m2 m2∈ms (there x∈xs) = inter m2 (there m2∈ms) x∈xs


  inv-addMove : {n k : ℕ} {c : Color} {playedMoves : Moves c k} {possible : Vec Move (suc n)} 
              → invariants playedMoves possible → (m : Move) → (m∈possible : m ∈ possible) 
              → ¬ WonC X (m ∷ playedMoves) → ¬ WonC O (m ∷ playedMoves) → k ≢ 8
              → invariants (m ∷ playedMoves) (vdelete m possible m∈possible)
  inv-addMove {n} {k} {c} {ms} {possible} 
              (c-inv n+k k<9 dist-m dist-v (part union inter) _)
              m m∈possible ¬WonX ¬WonO k≡8
              rewrite lem-plus-s n k
              = c-inv n+k 
                      (lem-≤-cases-ext (suc k) 9 k<9 (λ x → k≡8 (lem-suc-eq x))) 
                      (dist-cons dist-m (λ x → inter m x m∈possible))
                      (lem-delete-distinct-is-distinct m possible m∈possible dist-v) 
                      (part (union2 m m∈possible) 
                            (inter2 m m∈possible))
                      (¬WonX , ¬WonO)
                      where
                       union2 : (m0 : Move) (m0v : m0 ∈ possible) (m' : Move) → m' ∈' m0 ∷ ms ⊎ m' ∈ vdelete m0 possible m0v
                       union2 m0 m0v m2 with union m2
                       union2 m0 m0v m2 | inj₁ x = inj₁ (there x)
                       union2 m0 m0v m2 | inj₂ y' with m0 == m2
                       union2 m0 m0v m2 | inj₂ y' | yes p rewrite p = inj₁ here
                       union2 m0 m0v m2 | inj₂ y' | no ¬p = inj₂ (lem-delete-others m0v _==_ m2 ¬p y')

                       inter2 : (m : Move)(m∈possible : m ∈ possible)(m' : Move) → m' ∈' m ∷ ms → m' ∈ vdelete m possible m∈possible → ⊥
                       inter2 m m∈possible m2 m2∈m-ms m∈delete with m == m2
                       inter2 m m∈possible' m2 m2∈m-ms m∈delete | yes p rewrite p = 
                         lem-others-stay m2 possible m∈possible' dist-v m∈delete
                       inter2 m m∈possible' .m here m∈delete | no ¬p = ¬p refl
                       inter2 m m∈possible' m2 (there y') m∈delete | no ¬p = 
                         inter m2 y' (lem-delete-others-inv m∈possible' _==_ m2 ¬p m∈delete)

  ---------------------------
  --  Board types - Board  --
  ---------------------------

  record Board (n : ℕ) : Set where
    constructor c-board
    field
      currentPlayer : Color
      noPlayed      : ℕ
      playedMoves   : Moves currentPlayer noPlayed
      possibleMoves : Vec Move n
      inv           : invariants playedMoves possibleMoves     

  open Board
  module B = Board
--  open B

  absurdBoard : Board 0 → ⊥
  absurdBoard (c-board c k playedMoves possible (c-inv y y' y0 y1 y2 y3)) rewrite y = ten-nine y'

  ---------------------------------
  --  Board types - WorkerBoard  --
  ---------------------------------

  data WorkerBoard : Set where
    worker : {n : ℕ}                                               -- number of possible playedMoves
           → (b : Board n)
           → (m : Move)
           → .(m ∈ possibleMoves b)
--           → (m ∈ possibleMoves b)
           → WorkerBoard

  -- Commentary:
  -- The WorkerBoard represents a game that might have been concluded **just now**.

  -- Q: Why do we store the last move independently of moves (and possible)?
  -- A: This makes the task of implementing the undo operation trivial - all pieces are assembled.

  -- TODO: add m ∈ possible
  --       state that possible and moves form a partition of the Move type

  noWinnerW : WorkerBoard → Set
  noWinnerW (worker b m y) = noWinner (m ∷ B.playedMoves b) 

  wonW : Color → WorkerBoard → Set
  wonW c (worker b m y) = WonC c (m ∷ B.playedMoves b) 

  wMovesNo : WorkerBoard → ℕ
  wMovesNo (worker b m y) = suc (B.noPlayed b)

  -- no of possible moves BEFORE the last one

  wPossibleNo : WorkerBoard → ℕ
  wPossibleNo (worker {n} b m y) = n

  -----------------------------------
  --  Board types - FinishedBoard  --
  -----------------------------------

  data FinishedBoard : Set where
    draw : (wb : WorkerBoard) → .(wMovesNo wb ≡ 9) → .(noWinnerW wb) → FinishedBoard
    win  : (wb : WorkerBoard) → (c : Color)        → .(wonW c wb)    → FinishedBoard

  ------------------------
  --  Board operations  --
  ------------------------

  getResult : FinishedBoard → Result
  getResult (draw wb y y') = Draw
  getResult (win wb c y)   = Win c

  isEmpty : {n : ℕ} → Board n → Bool
  isEmpty {9} b = true
  isEmpty {_} b = false

  addMove : {n : ℕ} → (b : Board (suc n)) → (m : Move) → m ∈ possibleMoves b → Board n ⊎ FinishedBoard
  addMove b m m∈possible with checkGameStatus (B.playedMoves b) m (I.noWin (B.inv b)) (I.k<9 (B.inv b))

  addMove b m m∈possible | stWon winner loser 
    = inj₂ (win (worker b m m∈possible) (B.currentPlayer b) winner)

  addMove b m m∈possible | stDraw noWin k≡8 
    = inj₂ (draw (worker b m m∈possible) (cong suc k≡8) noWin)

  addMove b m m∈possible | stInProgress (¬WonX , ¬WonO) k≢8 
    = inj₁ (c-board _ _ (m ∷ B.playedMoves b) 
                        (vdelete m (B.possibleMoves b) m∈possible) 
                        (inv-addMove (B.inv b) m m∈possible 
                                     ¬WonX ¬WonO k≢8))


  undoWorker : (wb : WorkerBoard) → Board (wPossibleNo wb)
  undoWorker (worker b _ _) = b 

  undoFin : FinishedBoard → ∃ Board
  undoFin (draw wb _ _) = _ , undoWorker wb
  undoFin (win  wb _ _) = _ , undoWorker wb

  undo : {n : ℕ} → n < 9 → Board n → Board (suc n)

  undo n<9 (c-board .X .0 [] possible inv) 
    = ⊥-elim (inv-emptyBoard possible inv n<9)

  undo n<9 (c-board .(otherColor c) .(suc k) (_∷_ {c} {k} m ms) possible inv) 
    = c-board c k ms (m ∷ possible) (inv-undoMove inv)

  -----------------------
  --  Undo operations  --
  -----------------------

  dist-weak : ∀ {c n m}{ms : Moves c n} → distinct-m (m ∷ ms) → distinct-m ms
  dist-weak (dist-cons v-ms m∉ms) = v-ms

  distinctAll : distinct-v allMoves
  distinctAll = dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons dist-nil (λ ()))
    lem1) lem2) lem3) lem4) lem5) lem6) lem7) lem8 where
        lem1 : (x : P32 ∈ P33 ∷ []) → ⊥
        lem1 (there ())
                     
        lem2 : P31 ∈ P32 ∷ P33 ∷ [] → ⊥
        lem2 (there (there ()))
                             
        lem3 : P23 ∈ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem3 (there (there (there ())))
                                     
        lem4 : P22 ∈ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem4 (there (there (there (there ()))))
                                             
        lem5 : P21 ∈ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem5 (there (there (there (there (there ())))))
                                                     
        lem6 : P13 ∈ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem6 (there (there (there (there (there (there ()))))))
                                                             
        lem7 : P12 ∈ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem7 (there (there (there (there (there (there (there ())))))))
                                                                     
        lem8 : P11 ∈ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem8 (there (there (there (there (there (there (there (there ()))))))))

  empty : Board 9
  empty = c-board X zero [] allMoves (c-inv refl (s≤s z≤n) dist-nil distinctAll
          (part (λ m → inj₂ (allMovesValid m)) (λ m → λ ())) ((lem-won-empty X) , (lem-won-empty O))) 
