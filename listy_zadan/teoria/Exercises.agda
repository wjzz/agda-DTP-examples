module Exercises where

  module MartinLof where
    -- standard Martin-Lof type theory from Books

    data ℕ∅ : Set where

    N∅-elim : {P : Set}
            → ℕ∅
            → P
    N∅-elim ()

    ----

    data ℕ₁ : Set where
      0₁ : ℕ₁

    N₁-elim : {P : ℕ₁ → Set} 
            → P 0₁
            → (p : ℕ₁) → P p
    N₁-elim H0 0₁ = H0

    ----

    data ℕ₂ : Set where
      0₂ : ℕ₂
      1₂ : ℕ₂

    N₂-elim : {P : ℕ₂ → Set}
            → P 0₂ → P 1₂
            → (p : ℕ₂) → P p
    N₂-elim H0 H1 0₂ = H0
    N₂-elim H0 H1 1₂ = H1

    ----

    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ

    ----

    data Σ (A : Set) (B : A → Set) : Set where
      _,_ : (a : A) → B a → Σ A B

    Σ-elim : {A : Set} {B : A → Set} {P : Σ A B → Set}
           → ( (a : A) → (b : B a) → P (a , b) )
           → (p : Σ A B) → P p
    Σ-elim H (a , b) = H a b

    ----

    data Id (A : Set) (x : A) : A → Set where
      refl : Id A x x

    Id-elim : {A : Set} → {x y : A} → {P : A → Set}
            → Id A x y → P x → P y
    Id-elim refl H = H

    ---

    _×_ : Set → Set → Set
    A × B = Σ A (λ x → B)

    ×-elim : {A B : Set} {P : A × B → Set}
           → ( (a : A) → (b : B) → P (a , b) )
           → (p : A × B) → P p
    ×-elim = Σ-elim

    ---

--    open import Data.Product

{-
    c : {A B C : Set} → (A × B → C)
      → A → B → C
    c = λ f x y → f (x , y)

    u : {A B C : Set} → (A → B → C)
      → A × B → C
    u f p = ×-elim (λ a b → f a b) p

    test : {A B C : Set} → (f : A → B → C)
         → Id (A → B → C) (c (u f)) f
    test f = refl

    test2 : {A B C : Set} → (f : A × B → C)
          → Id (A × B → C) (u (c f))  f
    test2 f = refl
-}


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
