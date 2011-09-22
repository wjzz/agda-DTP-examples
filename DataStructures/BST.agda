module BST (Value : Set) where
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open Relation.Binary.PropositionalEquality.≡-Reasoning

Key : Set
Key = ℕ

module DybjersInternalBST where
  -- Binary Search Tree from "Dependent Types at Work"
  -- BST invariant : internal
  -- balanced      : no


  tot : (n m : ℕ) → n ≤ m ⊎ m ≤ n
  tot zero _          = inj₁ z≤n
  tot _   zero        = inj₂ z≤n
  tot (suc n) (suc m) with tot n m
  ... | inj₁ H = inj₁ $ s≤s H
  ... | inj₂ H = inj₂ $ s≤s H

  mutual
  
    data BSTree : Set where
      slf : BSTree 
      snd : (k : Key) (v : Value)
          → (l r : BSTree)
          → (l ≤T k)
          → (r ≥T k)
          → BSTree

    _≥T_ : BSTree → Key → Set
    slf               ≥T k0 = ⊤
    snd k v l r _ _   ≥T k0 = k0 ≤ k × l ≥T k0

    _≤T_ : BSTree → Key → Set
    slf               ≤T k0 = ⊤
    snd k v l r _ _   ≤T k0 = k ≤ k0 × r ≤T k0

  mutual

    sinsert : (k : Key) (v : Value) → BSTree → BSTree
    sinsert k v slf = snd k v slf slf tt tt 
    sinsert a v (snd x w l r pl pr) with (tot a x)
    ... | inj₁ p = snd x w (sinsert a v l) r (sins-leqT a x v l pl p) pr
    ... | inj₂ p = snd x w l (sinsert a v r) pl (sins-geqT a x v r pr p)

    sins-geqT : (a x : Key) (v : Value)
              → (t : BSTree)
              → t ≥T x 
              → x ≤ a
              → sinsert a v t ≥T x

    sins-geqT _ _ _ slf _ q = (q , tt)
    sins-geqT a x v (snd b bv l r _ _) (h1 , h2) q with tot a b
    ... | inj₁ H  = h1 , sins-geqT a x v l h2 q
    ... | inj₂ H  = h1 , h2

    sins-leqT : (a x : Key) (v : Value)
              → (t : BSTree)
              → t ≤T x
              → a ≤ x
              → (sinsert a v t) ≤T x

    sins-leqT _ _ _ slf _ q = (q , tt)
    sins-leqT a x v (snd b bv l r _ _) (h1 , h2) q with tot a b
    ... | inj₁ H = h1 , h2
    ... | inj₂ H = h1 , sins-leqT a x v r h2 q


module BalancedTree where
  open import Data.Bool
  -- Balanced trees
  -- inspired by AVL from Stdlib-0.5

  -- relation on heights
  -- n ~ m   iff |n-m| ≤ 1

  data ℕ₂ : Set where
    0₂ : ℕ₂
    1₂ : ℕ₂

  _+₂_ : ℕ₂ → ℕ → ℕ
  0₂ +₂ n = n
  1₂ +₂ n = suc n

  0+₂n : {n : ℕ} → 0₂ +₂ n ≡ n
  0+₂n = refl

  data _~_ : ℕ → ℕ → Set where
    B- : {n : ℕ} → suc n ~ n
    B0 : {n : ℕ} →     n ~ n
    B+ : {n : ℕ} →     n ~ suc n

  ~-max : {n m : ℕ} → n ~ m → ℕ
  ~-max (B- {n}) = suc n
  ~-max (B0 {n}) = n
  ~-max (B+ {n}) = suc n

  data BTree : ℕ → Set where
    leaf : BTree 0
    node : {hl hr : ℕ} 
         → (k : Key) (v : Value)
         → BTree hl
         → BTree hr
         → (bal : hl ~ hr)
         → BTree (suc $ ~-max bal)

  put- : {hr : ℕ}
       → (k : Key) (v : Value)
       → (l   : BTree (suc hr))
       → Σ ℕ₂ (λ i → BTree (i +₂ hr))
       → BTree (suc (suc hr))
  put- k v l (0₂ , r) = node k v l r B-
  put- k v l (1₂ , r) = node k v l r B0

  put+ : {hl : ℕ}
       → (k : Key) (v : Value)
       → Σ ℕ₂ (λ i → BTree (i +₂ hl))
       → (r   : BTree (suc hl))
       → BTree (suc (suc hl))
  put+ k v (0₂ , r) l = node k v l r B-
  put+ k v (1₂ , r) l = node k v l r B0

  put0 : {h : ℕ}
       → (k : Key) (v : Value)
       → Σ ℕ₂ (λ i → BTree (i +₂ h))
       → (r   : BTree h)
       → Σ ℕ₂ (λ i → BTree (i +₂ (suc h)))
  put0 {h} k v (0₂ , l) r = 0₂ , node k v l r B0
  put0 {h} k v (1₂ , l) r = 1₂ , node k v l r B-


  insert : {h : ℕ}
         → (k : Key) (v : Value)
         → (t : BTree h)
         → Σ ℕ₂ (λ i → BTree (i +₂ h))

  insert k v leaf = (1₂ , node k v leaf leaf B0)
  insert k v (node nk nv l r B-) = 0₂ , put- k v l (insert k v r)
  insert k v (node nk nv l r B0) = put0 k v (insert k v l) r
  insert k v (node nk nv l r B+) = 0₂ , put+ k v (insert k v l) r




{-
    inv_helper : {h : ℕ}
               → (k : Key) (v : Value)
               → (t : BTree h)
               → BTree (i +₂ h)
    inv_helper = _
-}

{-
open DybjersInternalBST



postulate
  v0 : Value
  v1 : Value
  v2 : Value

test0 = sinsert 0  v0 slf
test1 = sinsert 1  v1 test0
test2 = sinsert 2  v2 test1
-}
