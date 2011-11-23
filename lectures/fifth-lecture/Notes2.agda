module Notes2 where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

------------------------
--  Liczby naturalne  --
------------------------

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

---------------
--  Wektory  --
---------------

infixr 5 _∷_

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)


_++_ : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ v2 = v2
(x ∷ v1) ++ v2 = x ∷ (v1 ++ v2)         -- zamień nawiasy i pokaż zapętlenie


vreverse : {A : Set} {n : ℕ} → Vec A n → Vec A n
vreverse v = {!!}

----------------------------
--  Dowodzenie twierdzeń  --
----------------------------

infix 6 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

nat-plus-zero-l : (n : ℕ) → n + 0 ≡ n
nat-plus-zero-l zero = refl
nat-plus-zero-l (suc n) with nat-plus-zero-l n
... | rec = cong suc rec

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬_ : (A : Set) → Set
¬ A = A → ⊥

zero-not-one : ¬ (0 ≡ 1)
zero-not-one ()

n-not-suc-n : (n : ℕ) → ¬ (n ≡ suc n)
n-not-suc-n zero ()
n-not-suc-n (suc n) eq = n-not-suc-n n (lemma eq) where
  lemma : {n m : ℕ} → suc n ≡ suc m → n ≡ m
  lemma refl = refl

-- przyklad z vmap dla wektorow: plik Equations.agda

----------------------------
--  Predykaty indukcyjne  --
----------------------------

data Even : ℕ → Set where
  ev-0 : Even 0
  ev-s : {n : ℕ} → Even n → Even (suc (suc n))

sum-of-evens-is-even : ∀ {n m : ℕ} → Even n → Even m → Even (n + m)
sum-of-evens-is-even ev-0      p2 = p2
sum-of-evens-is-even (ev-s p1) p2 = ev-s (sum-of-evens-is-even p1 p2)

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) → (xs : List A) → List A

data EmptyList {A : Set} : List A → Set where
  empty : EmptyList []

-- inny sposob na wyspecifikowanie head

head : {A : Set} → (xs : List A) → ¬ (EmptyList xs) → A
head []       proof = ⊥-elim (proof empty)
head (x ∷ xs) proof = x

-- ok, ale jak sprawdzic czy lista jest pusta?

data Bool : Set where
  true false : Bool

isEmpty : {A : Set} → List A → Bool
isEmpty []       = true
isEmpty (x ∷ xs) = false

-- rozstrzygalne predykaty
-- można patrzeć na typ Dec jako na duży lepszy typ Bool
-- nie wystarcza nam wskazanie konstruktora, trzeba także podać odpowiedni *dowód*

-- Dec P ≈ P ∨ ¬P

data Dec (P : Set) : Set where
  yes : (p  :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

-- isEmpty jest rozstrzygalne

emptyDec : {A : Set} → (xs : List A) → Dec (EmptyList xs)
emptyDec []       = yes empty
emptyDec (x ∷ xs) = no (λ ())

-- jak używać takiej funkcji?

safeHead : {A : Set} → List A → Maybe A
safeHead xs with emptyDec xs
safeHead .[]      | yes empty = nothing
safeHead []       | no ¬p = ⊥-elim (¬p empty)
safeHead (x ∷ xs) | no ¬p = just x

-- sprawdzanie równości liczb naturalnych - słaba specyfikacja

nat-eq : ℕ → ℕ → Bool
nat-eq zero   zero     = true
nat-eq zero   (suc m)  = false
nat-eq (suc n) zero    = false
nat-eq (suc n) (suc m) = nat-eq n m

-- to samo, ale w wersji z silną specyfikacją

nat-eq-strong : (n m : ℕ) → Dec (n ≡ m)
nat-eq-strong zero zero = yes refl
nat-eq-strong zero (suc m) = no (λ ())
nat-eq-strong (suc n) zero = no (λ ())
nat-eq-strong (suc n) (suc m) with nat-eq-strong n m
nat-eq-strong (suc n) (suc m) | yes p = yes (cong suc p)
nat-eq-strong (suc n) (suc m) | no ¬p = no (λ x → ¬p (lemma x)) where
  lemma : {n m : ℕ} → suc n ≡ suc m → n ≡ m
  lemma refl = refl

-- przykłady przydatnych predykatów zdefiniowanych indukcyjnie

data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs}   → x ∈ (x ∷ xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

data _≤_ : ℕ → ℕ → Set where
  le-z : {n : ℕ}   → 0 ≤ n
  le-s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

data Sorted : List ℕ → Set where
  sorted-nil       : Sorted []
  sorted-singleton : (x : ℕ) → Sorted (x ∷ [])
  sorted-cons      : (x y : ℕ) (ys : List ℕ) 
                   → x ≤ y 
                   → Sorted (y ∷ ys) 
                   → Sorted (x ∷ y ∷ ys)


data Permutation {A : Set} : List A → List A → Set where
  perm-nil : Permutation [] []
 
  perm-cons : (x : A) → {xs ys : List A} 
                      → Permutation xs ys 
                      → Permutation (x ∷ xs) (x ∷ ys)
  
  perm-swap : (x y : A) → (xs : List A) 
                        → Permutation (x ∷ y ∷ xs) (y ∷ x ∷ xs)

{-
open import Data.Product

insert : {A : Set} → (x : A) → (xs : List A) 
       → Sorted xs
       → Σ[ ys : List A ]( Permutation (x∷xs) ys 
                         ∧ Sorted ys )
-}
