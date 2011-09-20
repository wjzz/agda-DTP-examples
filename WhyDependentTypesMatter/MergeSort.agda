module MergeSort where

open import Data.Nat
open import Data.Empty
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

decIf_then_else_ : {P Q : Set} → Dec P → Q → Q → Q
decIf (yes _) then t else e = t
decIf (no _)  then t else e = e

decIfF_then_else_ : {P Q : Set} → Dec P → (P → Q) → (¬ P → Q) → Q
decIfF (yes H) then t else e = t H
decIfF (no H)  then t else e = e H

module Version1 where
  open import Data.List

  -- first version of merge sort
  merge : List ℕ → List ℕ → List ℕ
  merge xs0 ys0 = aux xs0 ys0
    where
      aux : List ℕ → List ℕ → List ℕ
      aux [] [] = []
      aux [] ys = ys
      aux xs [] = xs
      aux (x ∷ xs) (y ∷ ys) with x ≤? y
      ... | yes _ = x ∷ merge xs   ys0
      ... | no _  = y ∷ merge xs0  ys

  deal : List ℕ → List ℕ × List ℕ
  deal []           = ([]     , [])
  deal (x ∷ [])     = (x ∷ [] , [])
  deal (l ∷ r ∷ xs) with deal xs
  ... | (ls , rs) = (l ∷ ls , r ∷ rs)

  sort : List ℕ → List ℕ
  sort xs with deal xs
  ... | (ls , []) = ls
  ... | (ls , rs) = merge (sort ls) (sort rs)


module Version2 where
  open import Data.List

  data Parity : Set where
    p₀ : Parity
    p₁ : Parity

  data DealT (X : Set) : Set where
    empT  : DealT X
    leafT : X → DealT X
    nodeT : Parity → DealT X → DealT X → DealT X

  insertT : {X : Set} → X → DealT X → DealT X
  insertT x empT      = leafT x
  insertT x (leafT y) = nodeT p₀ (leafT y) (leafT x)
  insertT x (nodeT p₀ l r) = nodeT p₁ (insertT x l) r
  insertT x (nodeT p₁ l r) = nodeT p₀ l (insertT x r)

  dealT : {X : Set} → List X → DealT X
  dealT []       = empT
  dealT (x ∷ xs) = insertT x (dealT xs)

  mergeT : DealT ℕ → List ℕ
  mergeT empT          = []
  mergeT (leafT x)     = x ∷ []
  mergeT (nodeT p l r) = Version1.merge (mergeT l) (mergeT r)

  sort : List ℕ → List ℕ
  sort xs = mergeT (dealT xs)


module Version3 where
  open import Data.Vec
  open Version2 using (Parity)
  open Version2.Parity

  plusZero : (n : ℕ) → n ≡ n + 0
  plusZero zero    = refl
  plusZero (suc n) = cong suc (plusZero n)

  plusSuc : (m n : ℕ) → suc (m + n) ≡ m + suc n
  plusSuc zero m    = refl
  plusSuc (suc n) m = cong suc (plusSuc n m)

  merge : {m n : ℕ} → Vec ℕ m → Vec ℕ n → Vec ℕ (m + n)
  merge [] ys = ys
  merge {suc m} (x ∷ xs) [] =
    subst (Vec ℕ) (plusZero (suc m)) (x ∷ xs)

  merge {suc m} {suc n} (x ∷ xs) (y ∷ ys) =
    decIf x ≤? y
      then x ∷ merge xs       (y ∷ ys)
      else (y ∷ subst (Vec ℕ) (plusSuc m n) (merge (x ∷ xs) ys))

  ⟦_⟧  : Parity → ℕ
  ⟦ p₀ ⟧  = 0
  ⟦ p₁ ⟧  = 1

  data DealT (X : Set) : ℕ → Set where
    empT  : DealT X 0
    leafT : X → DealT X 1
    nodeT : {n : ℕ} → (p : Parity) → DealT X (⟦ p ⟧ + n) → DealT X n 
          → DealT X (⟦ p ⟧ + n + n)

  mergeT : ∀ {n} → DealT ℕ n → Vec ℕ n
  mergeT empT          = []
  mergeT (leafT x)     = [ x ]
  mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)

  insertT : ∀ {X n} → X → DealT X n → DealT X (suc n)
  insertT x empT           = leafT x
  insertT x (leafT y)      = nodeT p₀ (leafT y) (leafT x)
  insertT x (nodeT p₀ l r) = nodeT p₁ (insertT x l) r
  insertT {X} x (nodeT {n} p₁ l r) =
    let
      r = nodeT p₀ l (insertT x r)
    in subst (DealT X) (sym $ plusSuc (suc n) n) r

  dealT : ∀ {X n} → Vec X n → DealT X n
  dealT []       = empT
  dealT (x ∷ xs) = insertT x (dealT xs)

  sort : ∀ {n} → Vec ℕ n → Vec ℕ n
  sort xs = mergeT (dealT xs)


module Version4 where
  open import Data.List
  open Version2.DealT
  open Version2 using (DealT; dealT)

  data OList : ℕ → Set where
    onil  : {b : ℕ}
          → OList b

    ocons : {b : ℕ} 
          → (x : ℕ)
          → b ≤ x
          → OList x
          → OList b

  merge : ∀ {b} → OList b → OList b → OList b
  merge onil ys = ys
  merge (ocons x blex xs') onil =
    ocons x blex xs'
  -- todo: termination
  merge (ocons x blex xs') (ocons y bley ys')
    with  (DecTotalOrder.total decTotalOrder x y)
  ... | inj₁ xley = ocons x blex (merge xs' (ocons y xley ys'))
  ... | inj₂ ylex = ocons y bley (merge (ocons x ylex xs') ys')

{-
  merge (ocons x blex xs') (ocons y bley ys') = 
    let
      f = λ (xley : x ≤ y) → ocons x blex (merge xs' (ocons y xley ys'))
      g = λ (ylex : y ≤ x) → ocons y bley (merge (ocons x ylex xs') ys')
    in [ f , g ]′ (DecTotalOrder.total decTotalOrder x y)
-}

  mergeT : DealT ℕ → OList 0
  mergeT empT      = onil
  mergeT (leafT x) = ocons x (z≤n) onil
  mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)


  sort : List ℕ → OList 0
  sort xs = mergeT (dealT xs)

