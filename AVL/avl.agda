{- AVL, inspired by AVL in standard library.
 -
 - Currently I am trying to add search tree invariant
 - to datatype
 -}

{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Relation.Binary

module avl (OrderedKeySet : StrictTotalOrder zero zero zero)
                (Value : Set)
                where

open StrictTotalOrder OrderedKeySet renaming (Carrier to Key)
open import Data.Product
open import Data.Maybe
open import Data.Bool
open import Data.Nat hiding (_<_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

module Invariants where

  data ℕ₂ : Set where
    0# : ℕ₂
    1# : ℕ₂

  infix 4 _~_

  data _~_ : ℕ → ℕ → Set where
    ~+ : ∀ {n} →     n ~ n + 1
    ~0 : ∀ {n} →     n ~ n
    ~- : ∀ {n} → 1 + n ~ n

  max : ∀ {m n} → m ~ n → ℕ
  max (~+ {n}) = suc n
  max (~0 {n}) = n
  max (~- {n}) = suc n


module Implementation where

  open Invariants

  KV : Set
  KV = Key × Value

  postulate
    keqdec : (k1 k2 : Key) -> k1 ≡ k2 

  mutual 
    data Tree : ℕ → Set  where
      leaf : Tree 0
      node : ∀ {hl hr} → (l : Tree hl) (kv : KV) (r : Tree hr) (bal : hl ~ hr)
           → ( (k : Key) → T(k ∈? l) → k < proj₁ kv)
           → Tree (1 + max bal)

    _∈?_ : ∀ {n} -> (k : Key) -> (t : Tree n) -> Bool
    _ ∈? leaf                          = false
    k ∈? (node {hl} {hr} l kv r bal H) = keqdec k (proj₁ kv)

{-
    data _∈_ : ∀ {n} -> Key -> Tree n -> Bool where

      in-node  : ∀ {hl hr} (k : Key) (v : Value)
               → (l : Tree hl) (r : Tree hr) (bal : hl ~ hr)
               → (H : ( (k' : Key) → T(k' ∈ l) → k' < k))
               → rue

      in-left  : ∀ {hl hr} (k : Key) (kv : KV)
               → (l : Tree hl) (r : Tree hr) (bal : hl ~ hr)
               → (H : ( (k : Key) → k ∈ l → k < proj₁ kv))
               → k ∈ l
               → k ∈ (node l kv r bal H)

      in-right : ∀ {hl hr} (k : Key) (kv : KV)
               → (l : Tree hl) (r : Tree hr) (bal : hl ~ hr)
               → (H : ( (k : Key) → k ∈ l → k < proj₁ kv))
               → k ∈ r
               → k ∈ (node l kv r bal H)
-}
