module WfRec where

open import Data.Nat
open import Data.List -- hiding -- (filter)
open import Data.Bool
open import Data.Product
open import Data.Empty
open import Relation.Nullary

-- ,,Kombinatory'' budujace nowe relacje sa inspirowane praca
-- L. C. Paulson -"Constructing Recursion Operators in Intuitionistic Type Theory" 
-- oraz roznymi jej implementacjami (biblioteka Coqa, Agdy)

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

  n≤n : {n : ℕ} → n ≤ n
  n≤n {zero}  = z≤n
  n≤n {suc n} = s≤s n≤n

  filter-length : {A : Set} (P : A → Bool)
                → (xs : List A) 
                → length (filter P xs) ≤ length xs
  filter-length P []       = z≤n
  filter-length P (x ∷ xs) with P x
  ... | true = s≤s (filter-length P xs)
  ... | false = trans≤ (filter-length P xs) suc≤

  div2 : ℕ → ℕ
  div2 zero          = zero
  div2 (suc zero)    = zero
  div2 (suc (suc n)) = suc (div2 n)

  div2≤ : {n : ℕ} → div2 n ≤ n
  div2≤ {zero} = z≤n
  div2≤ {suc zero} = z≤n
  div2≤ {suc (suc n)} with div2≤ {n}
  ... | H = s≤s (trans≤ H suc≤)

  div2s≤ : {n : ℕ} → div2 (suc n) < suc n
  div2s≤ {zero} = s≤s z≤n
  div2s≤ {suc zero} = s≤s div2s≤
  div2s≤ {suc (suc n)} with div2s≤ {n}
  ... | (s≤s H) = s≤s (s≤s (trans≤ H suc≤))

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


  WfNatInd : (P : ℕ → Set)
           → ( (x : ℕ) → ( (y : ℕ) → y < x → P y) → P x )
           → (x : ℕ) → P x
  WfNatInd P IH x = WfInd Wf< P IH x 


{- ----------------------------------------------------
   PRZYKLAD: logarytm binarny
-}

module WfNat_example where
  open WfNat

  log2 : ℕ → ℕ
  log2 = WfNatInd (λ x → ℕ) log2'
   where
     log2' : (n : ℕ) → ( (m : ℕ) → m < n → ℕ ) → ℕ
     log2' zero rec = zero
     log2' (suc zero) rec = zero
     log2' (suc n)    rec = suc (rec (div2 (suc n)) div2s≤)


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


{- ----------------------------------------------------
   Dobrze ufundowana relacja na porzadku leksykograficznym
-}

module WfLexProd
  (

    A    : Set
  ; _≺A_ : A → A → Set
  ; Wf≺A : Wf _≺A_

  ; B    : Set
  ; _≺B_ : B → B → Set
  ; Wf≺B : Wf _≺B_

  ) where

  data _≺A×B_ : A × B → A × B → Set where
    prodA : {a₁ a₂ : A} {b₁ b₂ : B}
          → a₁ ≺A a₂
          → (a₁ , b₁) ≺A×B (a₂ , b₂)

    prodB : {a : A} {b₁ b₂ : B}
          → b₁ ≺B b₂
          → (a , b₁) ≺A×B (a , b₂)

  prodη : {P : A × B → Set}
        → {p : A × B}
        → P (proj₁ p , proj₂ p)
        → P p
  prodη {P} {l , r} H = H

  mutual
    Acc1 : {a : A} {b : B} 
         → Acc _≺A_ a
         → Acc _≺A×B_ (a , b)
    Acc1 {a} {b} Ha = AccIntro (Acc2 Ha (Wf≺B b))

    Acc2 : {a : A} {b : B} 
         → Acc _≺A_ a
         → Acc _≺B_ b
         → (p : A × B)
         → p ≺A×B (a , b)
         → Acc _≺A×B_ p
    Acc2 (AccIntro fa) Hb ._ (prodA H) = Acc1 (fa _ H)
    Acc2 Ha (AccIntro fb) ._ (prodB H) = AccIntro (Acc2 Ha (fb _ H))
  
  Wf≺A×B : Wf _≺A×B_
  Wf≺A×B p = Acc1 (Wf≺A (proj₁ p))


{-
  WfInd : {A : Set} {_≺_ : A → A → Set} → (Wf _≺_)
         → (P : A → Set)
         → ( (x : A) → ( (y : A) → y ≺ x → P y ) → P x)
         → (x : A) → P x
-}

  WfProdInd : (P : A × B → Set)
            → ( (x : A × B) → ( (y : A × B) → y ≺A×B x → P y ) → P x)
            → (x : A × B) → P x
  WfProdInd = WfInd Wf≺A×B

{- ----------------------------------------------------
   Przyklad, Ackermann
-}

module WfLexProd_example where

  -- piekna definicja dla Agdy
  ackAgda : ℕ → ℕ → ℕ
  ackAgda  zero    n      = suc n
  ackAgda (suc m)  zero   = ackAgda m 1
  ackAgda (suc m) (suc n) = ackAgda m (ackAgda (suc m) n) 

  -- sprytna definicja dla Coqa
  ackCoq : ℕ → ℕ → ℕ
  ackCoq  zero   = suc
  ackCoq (suc m) = ackSM (ackCoq m)
   where
     ackSM : (ℕ → ℕ) → ℕ → ℕ
     ackSM ackM  zero   = ackM 1
     ackSM ackM (suc n) = ackM (ackSM ackM n)

  -- trudna definicja
  open WfNat
  open WfLexProd ℕ _<_ Wf< ℕ _<_ Wf< renaming (_≺A×B_ to _⊏_)

  ℕ² : Set
  ℕ² = ℕ × ℕ

  ackWf : ℕ → ℕ → ℕ
  ackWf m' n' = WfProdInd (λ x → ℕ) ack' (m' , n')
   where
     ack' : (x : ℕ²) → ( (y : ℕ²) → y ⊏ x → ℕ) → ℕ
     ack' (zero ,  n)     rec = suc n

     ack' (suc m , zero)  rec = rec (m , 1) proof1
       where
         proof1 = (prodA n≤n)

     ack' (suc m , suc n) rec = rec (m , rec (suc m , n) proof1) proof2
       where
         proof1 = prodB n≤n
         proof2 = prodA n≤n

------------------------------------------------------------------------------------------
open import Induction
open import Induction.Nat
open import Induction.WellFounded
