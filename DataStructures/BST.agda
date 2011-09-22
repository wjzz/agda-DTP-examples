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
  -- Binary Search Tree from "Dependent types at Work"
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
    sinsert a v (snd x w l r pl pr) with (tot x a)
    ... | inj₁ p = snd x w l (sinsert a v r) pl (sins-geqT a x v r pr p)
    ... | inj₂ p = snd x w (sinsert a v l) r (sins-leqT a x v l pl p) pr
  
    sins-geqT : (a x : Key) (v : Value)
              → (t : BSTree)
              → t ≥T x 
              → x ≤ a
              → sinsert a v t ≥T x

    sins-geqT _ _ _ slf _ q = (q , tt)
    sins-geqT a x v (snd b bv l r _ _) (h1 , h2) q with tot b a
    ... | inj₁ _  = (h1 , h2 )
    ... | inj₂ _  = (h1 , sins-geqT a x v l h2 q)

    sins-leqT : (a x : Key) (v : Value)
              → (t : BSTree)
              → t ≤T x
              → a ≤ x
              → (sinsert a v t) ≤T x

    sins-leqT _ _ _ slf _ q = (q , tt)
    sins-leqT a x v (snd b bv l r _ _) (h1 , h2) q with tot b a
    ... | inj₁ _ = (h1 , sins-leqT a x v r h2 q)
    ... | inj₂ _ = (h1 , h2)



open DybjersInternalBST

postulate
  v0 : Value
  v1 : Value
  v2 : Value

test0 = sinsert 0  v0 slf
test1 = sinsert 1  v1 test0
test2 = sinsert 2  v2 test1

-- some experiments
{-
module PlaceInvariants where
  open import Algebra
  open import Algebra.Structures
  import Algebra.FunctionProperties as P; open P _≡_
  

  data Place (X : Set) : Set where
    □0 : Place X
    □  : X → Place X

  □ℕ :  Place ℕ → ℕ
  □ℕ (□ k) = k
  □ℕ _     = 0

  ⊔-identity : Identity 0 _⊔_
  ⊔-identity = (λ _ → refl) , n⊔0≡n
    where
    n⊔0≡n : RightIdentity 0 _⊔_
    n⊔0≡n zero    = refl
    n⊔0≡n (suc n) = refl

  ⊔-assoc : Associative _⊔_
  ⊔-assoc zero    _       _       = refl
  ⊔-assoc (suc m) zero    o       = refl
  ⊔-assoc (suc m) (suc n) zero    = refl
  ⊔-assoc (suc m) (suc n) (suc o) = cong suc $ ⊔-assoc m n o

  ⊔3 : Place ℕ → Place ℕ → ℕ → Place ℕ
  ⊔3 l r t = □ $ □ℕ l ⊔ □ℕ r ⊔ t

  ⊔2 : Place ℕ → ℕ → Place ℕ
  ⊔2 i k = ⊔3 i i k

  _□<_ : Place ℕ → Place ℕ → Set
  _  □< □0   = ⊤
  □0 □< _    = ⊤
  □ l □< □ r = l < r

  _□<?_ : Decidable _□<_
  □0  □<? □0  = yes tt
  □0  □<? □ r = yes tt
  □ l □<? □0  = yes tt
  □ l □<? □ r with suc l ≤? r 
  ... | yes l<r = yes l<r
  ... | no  l≮r = no l≮r

  n⊔n : {n : ℕ} → n ≡ n ⊔ n
  n⊔n {zero}  = refl
  n⊔n {suc n} = subst (λ p → suc n ≡ suc p) (n⊔n {n}) (refl)

  ⊔3-last : (il ir : Place ℕ) (k : ℕ) → □ (□ℕ (⊔3 il ir k) ⊔ k) ≡ ⊔3 il ir k
  ⊔3-last il ir k = 
    begin
      □ (□ℕ (⊔3 il ir k) ⊔ k)
        ≡⟨ refl ⟩
      □ (□ℕ il ⊔ □ℕ ir ⊔ k ⊔ k)
        ≡⟨ refl ⟩
      □ ( ( ((□ℕ il) ⊔ (□ℕ ir)) ⊔ k)  ⊔  k)
        ≡⟨ {!!} ⟩
      □ ( (□ℕ il)   ⊔  ((□ℕ ir) ⊔ k) ⊔ k)
        ≡⟨ {!!} ⟩     
      ⊔3 il ir k
    ∎

module PlaceBST where
  open PlaceInvariants

  Key : Set
  Key = ℕ

  data Tree : Place Key → ℕ → Set where
    leaf : Tree □0 0

    node : ∀ {il hl ir hr} → (k : Key) (v : Value)
         → Tree il hl
         → Tree ir hr
         → il □< □ k
         → □ k □< ir
         → Tree (⊔3 il ir k) (suc $ hl ⊔ hr)

  data _∈_ : ∀ {i h} → Key → Tree i h → Set where

  insert : ∀ {i h}
         → (k : Key) → Value
         → Tree i h
         → ∃ λ h' → Tree (⊔2 i k) h'

  insert k v leaf =
    (1 , node k v leaf leaf tt tt)
  insert k v (node {il} {hl} {ir} {hr} k' v' tl tr ub lb)
    with k' ≟ k
  ... | yes k'=k = 
      let
        t  = node k' v' tl tr ub lb

        H : ⊔3 il ir k' ≡ □ (□ℕ il ⊔ □ℕ ir ⊔ k' ⊔ (□ℕ il ⊔ □ℕ ir ⊔ k') ⊔ k)
        H =
          begin
            ⊔3 il ir k'
              ≡⟨ {!!} ⟩
            □ (□ℕ il ⊔ □ℕ ir ⊔ k' ⊔ (□ℕ il ⊔ □ℕ ir ⊔ k') ⊔ k)
          ∎

        t'' = subst (λ p → Tree p $ suc (hl ⊔ hr)) H t

      in (suc (hl ⊔ hr) , t'')
                
  ... | no  _ = _
-}
