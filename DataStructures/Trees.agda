module Trees (Value : Set) where

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


module Balance where
  data ℕ₂ : Set where
    0₂ : ℕ₂
    1₂ : ℕ₂

  _+₂_ : ℕ₂ → ℕ → ℕ
  0₂ +₂ n = n
  1₂ +₂ n = suc n

  _-₂_ : ℕ₂ → ℕ → ℕ
  0₂ -₂ n     = n
  1₂ -₂ 0     = 0
  1₂ -₂ suc n = n

  -- relation on heights
  -- n ~ m   iff |n-m| ≤ 1
  data _~_ : ℕ → ℕ → Set where
    B- : {n : ℕ} → suc n ~ n
    B0 : {n : ℕ} →     n ~ n
    B+ : {n : ℕ} →     n ~ suc n

  ~-max : {n m : ℕ} → n ~ m → ℕ
  ~-max (B- {n}) = suc n
  ~-max (B0 {n}) = n
  ~-max (B+ {n}) = suc n

  nextH : {n m : ℕ} → n ~ m → ℕ
  nextH bal = suc $ ~-max bal

module BalancedTree where
  open Balance
  -- Balanced trees
  -- inspired by AVL from Stdlib-0.5


  data BTree : ℕ → Set where
    leaf : BTree 0
    node : {hl hr : ℕ} 
         → (k : Key)
         → BTree hl
         → BTree hr
         → (bal : hl ~ hr)
         → BTree (nextH bal)

  ---

  foldT : {A : ℕ → Set} {h : ℕ}
       → (aleaf : A 0)
       → (fnode : {hl hr : ℕ} → Key → A hl → A hr → (bal : hl ~ hr) → A (nextH bal))
       → BTree h
       → A h

  foldT aleaf fnode leaf              = aleaf
  foldT aleaf fnode (node nk l r bal) = 
    fnode nk
          (foldT aleaf fnode l)
          (foldT aleaf fnode r)
          bal

  --- 

  put- : {hr : ℕ}
       → (k : Key) 
       → (l   : BTree (suc hr))
       → Σ ℕ₂ (λ i → BTree (i +₂ hr))
       → BTree (suc (suc hr))
  put- k l (0₂ , r) = node k l r B-
  put- k l (1₂ , r) = node k l r B0

  put+ : {hl : ℕ}
       → (k : Key)
       → Σ ℕ₂ (λ i → BTree (i +₂ hl))
       → (r   : BTree (suc hl))
       → BTree (suc (suc hl))
  put+ k (0₂ , r) l = node k l r B-
  put+ k (1₂ , r) l = node k l r B0

  put0 : {h : ℕ}
       → (k : Key) 
       → Σ ℕ₂ (λ i → BTree (i +₂ h))
       → (r   : BTree h)
       → Σ ℕ₂ (λ i → BTree (i +₂ (suc h)))
  put0 {h} k (0₂ , l) r = 0₂ , node k l r B0
  put0 {h} k (1₂ , l) r = 1₂ , node k l r B-

  ---

  insert : {h : ℕ}
         → (k : Key)
         → (t : BTree h)
         → Σ ℕ₂ (λ i → BTree (i +₂ h))

  insert k leaf = (1₂ , node k leaf leaf B0)
  insert k (node nk  l r B-) = 0₂ , put- nk l (insert k r)
  insert k (node nk  l r B0) = put0 nk (insert k l) r
  insert k (node nk  l r B+) = 0₂ , put+ nk (insert k l) r


{-
  insertT : {hs hd : ℕ}
          → (ts : BTree hs)
          → (td : BTree hd)
          → Σ ℕ BTree
  insertT ts td = foldT {Σ ℕ BTree} (0 , leaf) f {!!}
   where
     f : ℕ → Σ ℕ BTree → Σ ℕ BTree → Σ ℕ BTree
     f k l r = {!!}
-}    

{-
  delete : {h : ℕ}
         → (k : Key)
         → (t : BTree h)
         → Σ ℕ₂ (λ i → BTree (i -₂ h))

  delete k leaf = 0₂ , leaf
  delete k (node nk l r B-) with n ≟ nk | delete k l | delete k r
  delete k (node nk l r B0) = {!!}
  delete k (node nk l r B+) = {!!}
-}

module Avl where
  -- AVL Trees, with BST and Balance invariants

  open Balance

  mutual
    data AvlTree : ℕ → Set where
      leaf : AvlTree 0
      node : {hl hr : ℕ}
           → (k : Key) (v : Value)
           → (l : AvlTree hl)
           → (r : AvlTree hr)
           → (l T< k)
           → (k <T r)
           → (b : hl ~ hr)
           → AvlTree (nextH b)

    _T<_ : {n : ℕ} → AvlTree n → Key → Set
    leaf                T< k0 = ⊤
    node k v l r _ _ _  T< k0 = k0 ≤ k × l T< k0

    _<T_ : {n : ℕ} → Key → AvlTree n → Set
    k0 <T leaf                = ⊤
    k0 <T node k v l r _ _ _  = k ≤ k0 × k0 <T r



  --- fix

  put- : {hr : ℕ}
       → (k : Key) (v : Value)
       → (l   : AvlTree (suc hr))
       → Σ ℕ₂ (λ i → Σ (AvlTree (i +₂ hr)) (λ r → k <T r))
       → l T< k
       → AvlTree (suc (suc hr))
  put- k v l (0₂ , r , k<Tr) l<Tk = node k v l r l<Tk k<Tr B-
  put- k v l (1₂ , r , k<Tr) l<Tk = node k v l r l<Tk k<Tr B0


  put+ : {hl : ℕ}
       → (k : Key) (v : Value)
       → Σ ℕ₂ (λ i → Σ (AvlTree (i +₂ hl)) (λ l → l T< k))
       → (r   : AvlTree (suc hl))
       → k <T r
       → AvlTree (suc (suc hl))
  put+ k v (0₂ , l , lT<k) r k<Tr = node k v l r lT<k k<Tr B+
  put+ k v (1₂ , l , lT<k) r k<Tr = node k v l r lT<k k<Tr B0


  put0 : {h : ℕ}
       → (k : Key) (v : Value)
       → Σ ℕ₂ (λ i → Σ (AvlTree (i +₂ h)) (λ l → l T< k))
       → (r   : AvlTree h)
       → k <T r
       → Σ ℕ₂ (λ i → AvlTree (i +₂ (suc h)))
  put0 {h} k v (0₂ , l , lT<k) r k<Tr = 0₂ , node k v l r lT<k k<Tr B0
  put0 {h} k v (1₂ , l , lT<k) r k<Tr = 1₂ , node k v l r lT<k k<Tr B-

  ---

  total : (n m : ℕ) → n ≡ m ⊎ n < m ⊎ m < n
  total zero zero       = inj₁ refl
  total zero (suc m)    = inj₂ (inj₁ $ s≤s z≤n)
  total (suc n) zero    = inj₂ (inj₂ $ s≤s z≤n)
  total (suc n) (suc m) with total n m
  ... | inj₁ H        = inj₁ (cong suc H)
  ... | inj₂ (inj₁ H) = inj₂ $ inj₁ $ s≤s H
  ... | inj₂ (inj₂ H) = inj₂ $ inj₂ $ s≤s H

  ---

  rotate-LR : {hl hr hll hlr hlrl hlrr : ℕ}
            → (k kl klr : ℕ)
            → (r   : AvlTree hr)
            → (ll  : AvlTree hll)
            → (lrl : AvlTree hlrl)
            → (lrr : AvlTree hlrr)
            → (l~r     : hl   ~ hr)
            → (lrl~lrr : hlrl ~ hlrr)
            → Σ ℕ₂ (λ i → AvlTree (i +₂ nextH l~r))

  rotate-LR k kl klr r ll lrl lrr lbr = {!!}

  ---

  insert : {h : ℕ}
         → (k : Key) (v : Value)
         → (t : AvlTree h)
         → Σ ℕ₂ (λ i → AvlTree (i +₂ h))
  insert k v leaf = 1₂ , node k v leaf leaf tt tt B0
  insert k v (node nk nv l r lT<nk nk<Tr bal) 
    with total k nk | insert k v l | insert k v r
  ... | inj₁ k≡nk        | _ | _ = 0₂ , node nk v l r lT<nk nk<Tr bal
  ... | inj₂ (inj₁ k<nk) | _ | _ = {!!}
  ... | inj₂ (inj₂ nk<k) | _ | _ = {!!}




open Balance
open BalancedTree

postulate
  v0 : Value
  v1 : Value
  v2 : Value
  v3 : Value

test0 = proj₂ $ insert 0  leaf
test1 = proj₂ $ insert 1  test0
test2 = proj₂ $ insert 2  test1
test3 = proj₂ $ insert 3  test2
test4 = proj₂ $ insert 3  test3
test5 = proj₂ $ insert 3  test4
test6 = proj₂ $ insert 0  test5

