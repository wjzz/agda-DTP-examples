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

module DybjersInternalBST where
  -- Binary Search Tree from "Dependent Types at Work"
  -- BST invariant : internal
  -- balanced      : no

  Key : Set
  Key = ℕ

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



open DybjersInternalBST

postulate
  v0 : Value
  v1 : Value
  v2 : Value

test0 = sinsert 0  v0 slf
test1 = sinsert 1  v1 test0
test2 = sinsert 2  v2 test1
