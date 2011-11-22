module WfRec where

open import Data.Nat
open import Data.List -- hiding -- (filter)
open import Data.Bool
open import Data.Empty
open import Relation.Nullary

{- ----------------------------------------------------
   Rozne pomoce
-}

module StdLib where

  trans≤ : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  trans≤ z≤n Hbc = z≤n
  trans≤ (s≤s m≤n) (s≤s m≤n') = s≤s (trans≤ m≤n m≤n')

  suc≤ : {n : ℕ} → n ≤ suc n
  suc≤ {zero} = z≤n
  suc≤ {suc n} = s≤s suc≤

  No0< : {n : ℕ} → n < 0 → ⊥
  No0< ()

  filter-length : {A : Set} (P : A → Bool)
                → (xs : List A) 
                → length (filter P xs) ≤ length xs
  filter-length P []       = z≤n
  filter-length P (x ∷ xs) with P x
  ... | true = s≤s (filter-length P xs)
  ... | false = trans≤ (filter-length P xs) suc≤

open StdLib

{- ----------------------------------------------------
   Dobrze ufundowana indukcja
-}

module Wf where

  data Acc {A : Set} (_≺_ : A → A → Set) : A → Set where
    AccIntro : {x : A} 
              → ( (y : A) → y ≺ x → Acc _≺_ y )
              → Acc _≺_ x

  AccInd : {A : Set} {_≺_ : A → A → Set}
          → (P : A → Set)
          → ( ( x : A )
            → ( (y : A) → y ≺ x → Acc _≺_ y )
            → ( (y : A) → y ≺ x → P y )
            → P x
            )
          → (x : A) → Acc _≺_ x → P x
  AccInd P IH x (AccIntro f) = IH x f (λ y Hy → AccInd P IH y (f y Hy))


  Wf : {A : Set} → (_≺_ : A → A → Set) → Set
  Wf {A} _≺_ = (x : A) → Acc _≺_ x

  WfInd : {A : Set} {_≺_ : A → A → Set} → (Wf _≺_)
         → (P : A → Set)
         → ( (x : A) → ( (y : A) → y ≺ x → P y ) → P x)
         → (x : A) → P x

  WfInd {A} {_≺_} Wf≺ P IH x = AccInd P (λ x f → IH x ) x (Wf≺ x)

open Wf

{- ----------------------------------------------------
   Relacja ostrego porzadku na liczbach naturalnych 
   jest dobrze ufundowana
-}

module WfNat where

  Acc0 : Acc _<_ 0
  Acc0 = AccIntro (λ y Hy → ⊥-elim (No0< Hy))

  AccSn : {n : ℕ} → Acc _<_ n → Acc _<_ (suc n)
  AccSn {zero} H = AccIntro (λ y Hy → spec Hy)
   where
     spec : {y : ℕ} → y < 1 → Acc _<_ y
     spec (s≤s z≤n) = Acc0

  AccSn {suc n} (AccIntro f) = AccIntro (λ y Hy → spec Hy)
   where
     spec : {y : ℕ} → y < suc (suc n) → Acc _<_ y
     spec {y} (s≤s m≤n) = AccIntro (λ z Hz → f z  (trans≤ Hz m≤n))

  Wf< : Wf _<_
  Wf< zero = Acc0 
  Wf< (suc n) with Wf< n
  ... | H = AccSn H


{- ----------------------------------------------------
   Dobrze ufundowana relacja na przeciw-obrazie
-}

module WfInvImage
  (
    B    : Set
  ; _≺B_ : B → B → Set
  ; Wf≺B : Wf _≺B_

  ; A    : Set
  ; h    : A → B

  ) where

  _≺A_ : A → A → Set
  a₁ ≺A a₂ = h a₁ ≺B h a₂

  AccA : {x : A} → Acc _≺B_ (h x) → Acc _≺A_ x
  AccA {x} (AccIntro f) = AccIntro (λ y Hy → AccA (f (h y) Hy))
 
  Wf≺A : Wf _≺A_
  Wf≺A a = AccA (Wf≺B (h a))


{- ----------------------------------------------------
   PRZYKLAD: specjalizacja zasady dobrze ufundowanej
             rekursji dla list
-}

module WfInvImage_example (X : Set)  where

  open import Data.List
  open WfNat public
  open WfInvImage ℕ _<_ Wf< (List X) length public renaming (_≺A_ to _⊏_ ; Wf≺A to Wf⊏) 

{-
  WfInd : {A : Set} {_≺_ : A → A → Set} → (Wf _≺_)
         → (P : A → Set)
         → ( (x : A) → ( (y : A) → y ≺ x → P y ) → P x)
         → (x : A) → P x
-}

  WfListInd : (P : List X → Set)
            → ( (x : List X) → ( (y : List X) → y ⊏ x → P y ) → P x)
            → (x : List X) → P x
  WfListInd = WfInd Wf⊏

{- ----------------------------------------------------
   PRZYKLAD: latwy do napisania quicksort
-}

module QuickSort where

  open WfInvImage_example ℕ

  before : ℕ → ℕ → Bool
  before c x with x ≤? c
  ... | yes p = true
  ... | no ¬p = false

  after : ℕ → ℕ → Bool
  after c y with suc c ≤? y
  after c y | yes p = true
  after c y | no ¬p = false

  qless : (pf : ℕ → Bool)
        → (a  : ℕ)
        → (l  : List ℕ)
        → filter pf l ⊏ (a ∷ l)
  qless pf a l = s≤s (filter-length pf l)

  qsort : List ℕ → List ℕ
  qsort = WfListInd (λ x → List ℕ) qsort'
   where
     qsort' : (xs : List ℕ) → ( (ys : List ℕ) → ys ⊏ xs → List ℕ ) → List ℕ
     qsort' [] rec = []
     qsort' (x ∷ xs) rec = left ++ x ∷ right
      where
        left  = rec (filter (before x) xs) (qless (before x) x xs)
        right = rec (filter (after x) xs) (qless (after x) x xs)

  test = qsort ( 2 ∷ 9 ∷ 7 ∷ 1 ∷ [] )

------------------------------------------------------------------------------------------
open import Induction
open import Induction.Nat
open import Induction.WellFounded


module Lib where
{-
  filter : {A : Set} → (P : A → Bool) → List A → List A
  filter P [] = []
  filter P (x ∷ xs) with P x
  ... | true  = x ∷ filter P xs
  ... | false = filter P xs

-}

  ≤suc : {n : ℕ} → n ≤ suc n
  ≤suc {zero} = z≤n
  ≤suc {suc n} = s≤s ≤suc

  _<L_ : {A : Set} → List A → List A → Set
  xs <L ys = length xs < length ys


module QSort where
  open Lib

  qless : {A  : Set} 
        → (pf : A → Bool)
        → (a  : A)
        → (l  : List A)
        → filter pf l <L (a ∷ l)
  qless pf a l = s≤s (filter-length pf l)

  before : ℕ → ℕ → Bool
  before c x with x ≤? c
  ... | yes p = true
  ... | no ¬p = false

  after : ℕ → ℕ → Bool
  after c y with suc c ≤? y
  after c y | yes p = true
  after c y | no ¬p = false

  s : (l : List ℕ) → ( (l' : List ℕ) → l' <L l → List ℕ) → List ℕ
  s [] ih = []
  s (a ∷ l) ih = ih (filter (before a) l) (qless (before a) a l) 
               ++ a ∷ ih (filter (after a) l) (qless (after a) a l)

  data DealT : List ℕ → Set where
    emptyT : DealT []
    stepT  : {a : ℕ} {xs : List ℕ}
           → DealT (filter (before a) xs)
           → DealT (filter (after a) xs)
           → DealT (a ∷ xs)

