module Cantor where

open import Data.Product 
open import Data.Nat
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

negb : Bool → Bool
negb true  = false
negb false = true

Hnegb : (b : Bool) → ¬ b ≡ negb b
Hnegb true ()
Hnegb false ()

BinSeq : Set
BinSeq = ℕ → Bool

Σ-elim : {A : Set} {B : A → Set} {P : Σ A B → Set}
       → ( (a : A) → (b : B a) → P (a , b) )
       → (p : Σ A B) → P p
Σ-elim H (a , b) = H a b

thm : ¬ ∃ λ (f : ℕ → BinSeq) → ∃ λ (g : BinSeq → ℕ)
    → ( (s : BinSeq) → f (g s) ≡ s )
thm H = Σ-elim (λ f H' → Σ-elim (λ g H'' → diagonal f g H'') H') H
 where

   diagonal : (f : ℕ → BinSeq) (g : BinSeq → ℕ) 
            → ( (s : BinSeq) → f (g s) ≡ s )
            → ⊥
   diagonal f g C = Hnegb (h nh) Heq
    where
      h : BinSeq
      h n = negb (f n n)

      nh = g h

      Heq : negb (f (g h) nh) ≡ negb (h nh)
      Heq = subst (λ p → negb (p nh) ≡ (negb (h nh))) (sym (C h)) refl
