module ExercisesPaper where

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

    ℕ₁-elim : {P : ℕ₁ → Set} 
            → P 0₁
            → (p : ℕ₁) → P p
    ℕ₁-elim H0 0₁ = H0

    ----

    data ℕ₂ : Set where
      0₂ : ℕ₂
      1₂ : ℕ₂

    ℕ₂-elim : {P : ℕ₂ → Set}
            → P 0₂ → P 1₂
            → (p : ℕ₂) → P p
    ℕ₂-elim H0 H1 0₂ = H0
    ℕ₂-elim H0 H1 1₂ = H1

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

    syntax Σ A (λ x → B) = Σ[ x ∶ A ] B
    ----

    data _≡_ {A : Set} (x : A) : A → Set where
      refl :  x ≡ x

    ≡-elim : {A : Set} → {x y : A} → (P : A → Set)
            → x ≡ y → P x → P y
    ≡-elim P refl H = H

    ---

    _×_ : Set → Set → Set
    A × B = Σ A (λ x → B)

    ×-elim : {A B : Set} {P : A × B → Set}
           → ( (a : A) → (b : B) → P (a , b) )
           → (p : A × B) → P p
    ×-elim = Σ-elim

    ---

    ¬_ : (P : Set) → Set
    ¬ P = P → ℕ∅

    ---

    mutual
      data U : Set where
        n₀ : U
        n₁ : U
        n₂ : U
--        _⊕_ : U -> U -> U
        σ : (a : U) -> (T a -> U) -> U
        π : (a : U) -> (T a -> U) -> U
        N : U
--      w : (a : U) -> (T a -> U) -> U
        i : (a : U) -> T a -> T a -> U

      T : U -> Set
      T n₀        = ℕ∅
      T n₁        = ℕ₁
      T n₂        = ℕ₁
--      T (a ⊕ b)   = T a + T b
      T (σ a b)   = Σ (T a) (\x -> T (b x))
      T (π a b)   = (x : T a) -> T (b x)
      T N         = ℕ
--      T (w a b)   = W (T a) (\x -> T (b x))
      T (i a b c) = b ≡ c

  module Task1 where
    open MartinLof

    term1 : {A : Set} {C : A → A → Set} 
          → ( (x : A) → (y : A) → C x y )
          → (y : A) → (x : A) → C x y
    term1 f y x = f x y

    term2 : {A : Set} {C : A → A → Set} 
          → ( Σ[ x ∶ A ] ((y : A) → C x y) )
          → (y : A) → Σ[ x ∶ A ] C x y
    term2 p y = Σ-elim (λ x f → (x , f y) ) p


  module Task2 where
    open MartinLof

    sym : {A : Set} → {x y : A}
         → x ≡ y
         → y ≡ x
    sym refl = refl

    cong : {A B : Set} → {x y : A}
         → (f : A → B)
         → x ≡ y
         → f x ≡ f y
    cong f refl = refl

  module Task8 where
    open MartinLof
    open Task2


    negb : ℕ₂ → ℕ₂
    negb = λ b → ℕ₂-elim 1₂ 0₂ b

    Hnegb : (b : ℕ₂) → ¬ (b ≡ negb b)
    Hnegb = λ b → ℕ₂-elim ? ? b
     where
       H01 : ¬ (0₂ ≡ 1₂)
       H01 H = Hxy
        where
          isZ : ℕ₂ → Set
          isZ b = T (ℕ₂-elim n₁ n₀ b)

          Hxy : isZ 1₂
          Hxy = ≡-elim isZ H 0₁


  module Task_Cantor where
    open MartinLof

    negb : ℕ₂ → ℕ₂
    negb = λ b → ℕ₂-elim 1₂ 0₂ b

    Hnegb : (b : ℕ₂) → ¬ (b ≡ negb b)
    Hnegb 0₂ ()
    Hnegb 1₂ ()

    BinSeq : Set
    BinSeq = ℕ → ℕ₂

    thm : ¬ Σ (ℕ → BinSeq) (λ f  → Σ (BinSeq → ℕ) ( λ g
        → ( (s : BinSeq) → s ≡ f (g s) )))
    thm H = Σ-elim (λ f H' → Σ-elim (λ g H'' → diagonal f g H'') H') H
      where
        diagonal : (f : ℕ → BinSeq) (g : BinSeq → ℕ) 
                 → ( (s : BinSeq) → s ≡ f (g s) )
                 → ℕ∅
        diagonal f g C = Hnegb (h nh) Heq
          where
            h : BinSeq
            h n = negb (f n n)

            nh = g h

            Heq : negb (f (g h) nh) ≡ negb (h nh)
            Heq = ≡-elim (λ p → negb (p nh) ≡ (negb (h nh))) (C h) refl
