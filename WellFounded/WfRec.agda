module WfRec where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Empty
open import Relation.Nullary

-- ,,Kombinatory'' budujace nowe relacje sa inspirowane praca
-- L. C. Paulson -"Constructing Recursion Operators in Intuitionistic Type Theory" 
-- oraz roznymi implementacjami tych kombinatorow (biblioteka Coqa, Agdy)

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

  take-length : {A : Set} 
              → (n : ℕ)
              → (xs : List A)
              → length (take n xs) ≤ length xs
  take-length zero xs          = z≤n
  take-length (suc n) []       = z≤n
  take-length (suc n) (x ∷ xs) = s≤s (take-length n xs)

  drop-length : {A : Set} 
              → (n : ℕ)
              → (xs : List A)
              → length (drop n xs) ≤ length xs
  drop-length zero xs          = n≤n
  drop-length (suc n) []       = z≤n
  drop-length (suc n) (x ∷ xs) = trans≤ (drop-length n xs) suc≤

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

  minus≤ : (n m : ℕ)
         → n ∸ m ≤ n
  minus≤ n        zero   = n≤n
  minus≤ zero    (suc m) = z≤n
  minus≤ (suc n) (suc m) = trans≤ (minus≤ n m) suc≤





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
  Acc0 = AccIntro (λ y Hy<0 → ⊥-elim (No0< Hy<0))

  AccSn : {n : ℕ} → Acc _<_ n → Acc _<_ (suc n)
  AccSn {zero} Hn = AccIntro (λ y Hy<1 → spec Hy<1)
   where
     spec : {y : ℕ} → y < 1 → Acc _<_ y
     spec (s≤s z≤n) = Acc0

  AccSn {suc n} (AccIntro f) = AccIntro (λ y Hy<Sn → spec Hy<Sn)
   where
     spec : {y : ℕ} → y < suc (suc n) → Acc _<_ y
     spec {y} (s≤s y≤Sn) = AccIntro (λ z HSz<n → f z  (trans≤ HSz<n y≤Sn))

  Wf< : Wf _<_
  Wf< zero = Acc0 
  Wf< (suc n) with Wf< n
  ... | H = AccSn H

{-
  WfInd : {A : Set} {_≺_ : A → A → Set} → (Wf _≺_)
         → (P : A → Set)
         → ( (x : A) → ( (y : A) → y ≺ x → P y ) → P x)
         → (x : A) → P x
-}

  WfNatInd : (P : ℕ → Set)
           → ( (x : ℕ) → ( (y : ℕ) → y < x → P y) → P x )
           → (x : ℕ) → P x

  WfNatInd P IH x = WfInd Wf< P IH x 


{- ----------------------------------------------------
   PRZYKLAD: logarytm binarny
-}

module WfNat_example where
  open WfNat

{-
  log2 0  = zero
  log2 1  = zero
  log2 n  = suc (div2 n)
-}

  log2 : ℕ → ℕ
  log2 = WfNatInd (λ x → ℕ) log2'
   where
     log2' : (n : ℕ) → ( (m : ℕ) → m < n → ℕ ) → ℕ
     log2' zero rec       = zero
     log2' (suc zero) rec = zero
     log2' (suc n)    rec = suc (rec (div2 (suc n)) proof1)
      where
        proof1 = div2s≤

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



module MergeSort1 where

  -- kod z poprzedniego wykladu M.Mielowskiego

  data Order : Set where
    le : Order
    ge : Order


  order : (x y : ℕ) → Order
  order  zero     y       = le
  order (suc x′)  zero    = ge
  order (suc x′) (suc y′) = order x′ y′

  merge : (xs ys : List ℕ) → List ℕ
  merge  []      ys = ys
  merge (x ∷ xs) [] = x ∷ xs
  merge (x ∷ xs) (y ∷ ys) with order x y | x ∷ merge xs (y ∷ ys) | y ∷ merge (x ∷ xs) ys
  ... | le | m1 | m2 = m1
  ... | ge | m1 | m2 = m2


  data Parity : Set where
    odd  : Parity
    even : Parity

  data DealT (A : Set) : Set where
    empT  : DealT A
    leafT : A → DealT A
    nodeT : (p : Parity) → (l r : DealT A) → DealT A

  insertT : {A : Set}(x : A) → (t : DealT A) → DealT A
  insertT x  empT            = leafT x
  insertT x (leafT y)        = nodeT even (leafT y) (leafT x)
  insertT x (nodeT even l r) = nodeT odd (insertT x l) r
  insertT x (nodeT odd  l r) = nodeT even l (insertT x r)

  dealT : {A : Set}(xs : List A) → DealT A
  dealT    []    = empT
  dealT (x ∷ xs) = insertT x (dealT xs)

  mergeT : (t : DealT ℕ) → List ℕ
  mergeT  empT         = []
  mergeT (leafT x)     = x ∷ []
  mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)

  sort′ : List ℕ → List ℕ
  sort′ xs = mergeT (dealT xs)

module MergeSortWf where

  open WfInvImage_example ℕ

  half1 : List ℕ → List ℕ
  half1 xs = take (div2 (length xs)) xs

  half2 : List ℕ → List ℕ
  half2 xs = drop (div2 (length xs)) xs
  
  merge : List ℕ → List ℕ → List ℕ
  merge [] ys             = ys
  merge xs []             = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤? y | merge xs (y ∷ ys) | merge (x ∷ xs) ys
  ... | yes _ | rsx | _   = x ∷ rsx
  ... | no  _ | _   | rsy = y ∷ rsy

  msort : List ℕ → List ℕ
  msort  = WfListInd _ msort' 
   where
     msort' : (xs : List ℕ) → ( (ys : List ℕ) → ys ⊏ xs → List ℕ) → List ℕ
     msort' [] rec                = []
     msort' (x ∷ [])     rec      = x ∷ []
     msort' (a ∷ b ∷ xs) rec      = merge left right
       where
         left  = rec (half1 (a ∷ b ∷ xs)) {!!}
         right = rec (half2 (a ∷ b ∷ xs)) {!!}


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

  -- definicja opierajaca sie o Wf
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
         proof1 = prodA n≤n

     ack' (suc m , suc n) rec = rec (m , rec (suc m , n) proof1) proof2
       where
         proof1 = prodB n≤n
         proof2 = prodA n≤n


{- ----------------------------------------------------
   Przechodnie domkniecie
-}

module WfTransClo
  (
    A    : Set
  ; _≺_ : A → A → Set
  ; Wf≺ : Wf _≺_
  ) where

  data _≺⁺_ : A → A → Set where
    step : {a b c : A}
         → a ≺  b
         → a ≺⁺ b

    many : {a b c : A}
         → a ≺⁺ b
         → b ≺⁺ c
         → a ≺⁺ c

  mutual
    Acc1 : {a : A} → Acc _≺_ a → Acc _≺⁺_ a
    Acc1 H = AccIntro (λ y Hy≺⁺a → Acc2 H Hy≺⁺a)

    Acc2 : {a b : A} → Acc _≺_ a → b ≺⁺ a → Acc _≺⁺_ b
    Acc2 {a} {b} (AccIntro fa) (step Ha≺b)       = Acc1 (fa b Ha≺b)
    Acc2 {a} {b} Ha (many Ha≺⁺b Hb≺⁺c)           = helper (Acc2 Ha Hb≺⁺c) Ha≺⁺b
     where
       helper : {p q : A} → Acc _≺⁺_ p → q ≺⁺ p → Acc _≺⁺_ q
       helper (AccIntro fp) Hq≺⁺p = AccIntro (λ s Hs≺⁺q → fp s (many Hs≺⁺q Hq≺⁺p))

  Wf≺⁺ : Wf _≺⁺_
  Wf≺⁺ x = Acc1 (Wf≺ x)

