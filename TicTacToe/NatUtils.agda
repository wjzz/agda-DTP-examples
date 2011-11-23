module NatUtils where

open import Data.Nat hiding (compare)

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-------------------------------------
--  Properties of equlity on nats  --
-------------------------------------

lem-zero-neq-suc : ∀ {n} → 0 ≢ suc n
lem-zero-neq-suc ()

lem-suc-eq : ∀ {n k : ℕ} → suc n ≡ suc k → n ≡ k
lem-suc-eq refl = refl

{- BASE arith lem-zero-neq-suc lem-suc-eq -}

-------------------------------------
--  Properties of addition (_+_)   --
-------------------------------------

lem-plus-0-n : (n : ℕ) → 0 + n ≡ n
lem-plus-0-n n = refl

lem-plus-n-0 : (n : ℕ) → n + 0 ≡ n
lem-plus-n-0 zero    = refl
lem-plus-n-0 (suc n) = cong suc (lem-plus-n-0 n)

lem-plus-1-n : (n : ℕ) → 1 + n ≡ n + 1
lem-plus-1-n zero = refl
lem-plus-1-n (suc n) = cong suc (lem-plus-1-n n)

lem-plus-s : (n m : ℕ) → suc (n + m) ≡ n + suc m
lem-plus-s zero m = refl
lem-plus-s (suc n) m = cong suc (lem-plus-s n m)

lem-plus-comm : (n m : ℕ) → n + m ≡ m + n
lem-plus-comm zero m = sym (lem-plus-n-0 m)
lem-plus-comm (suc n) m = trans (cong suc (lem-plus-comm n m)) (lem-plus-s m n)

lem-plus-assoc : (k l n : ℕ) → (k + l) + n ≡ k + (l + n)
lem-plus-assoc zero l n = refl
lem-plus-assoc (suc n) l n' = cong suc (lem-plus-assoc n l n')

{- BASE arith lem-plus-n-0 lem-plus-1-n lem-plus-s lem-plus-comm lem-plus-assoc -}

------------------------------------------
--  Properties of multiplication (_*_)  --
------------------------------------------

lem-mult-0-n : (n : ℕ) → 0 * n ≡ 0
lem-mult-0-n n = refl

lem-mult-n-0 : (n : ℕ) → n * 0 ≡ 0
lem-mult-n-0 zero = refl
lem-mult-n-0 (suc n) = lem-mult-n-0 n

lem-mult-1-n : (n : ℕ) → 1 * n ≡ n
lem-mult-1-n n = lem-plus-n-0 n

lem-mult-n-1 : (n : ℕ) → n * 1 ≡ n
lem-mult-n-1 zero = refl
lem-mult-n-1 (suc n) = cong suc (lem-mult-n-1 n)

lem-mult-plus : (k n m : ℕ) → (k + n) * m ≡ k * m + n * m
lem-mult-plus zero n m = refl
lem-mult-plus (suc k) n m = trans (cong (λ x → m + x) (lem-mult-plus k n m)) (sym (lem-plus-assoc m (k * m) (n * m)))

lem-mult-assoc : (k n m : ℕ) → (k * n) * m ≡ k * (n * m)
lem-mult-assoc zero n m = refl
lem-mult-assoc (suc k) n m = trans (lem-mult-plus n (k * n) m) (cong (λ x → n * m + x) (lem-mult-assoc k n m))

{- BASE arith lem-mult-n-0 lem-mult-n-1 lem-mult-assoc -}

-------------------------------
--  Even and odd predicates  --
-------------------------------

data Even : ℕ → Set where
  ev-0 : Even 0
  ev-s : forall {n} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  odd : ∀ {n} → Even n → Odd (suc n)


lem-plus-of-evens : ∀ {n m} → Even n → Even m → Even (n + m)
lem-plus-of-evens ev-0 p2 = p2
lem-plus-of-evens (ev-s p1) p2 = ev-s (lem-plus-of-evens p1 p2)

lem-plus-of-odds : ∀ {n m} → Odd n → Odd m → Even (n + m)
lem-plus-of-odds {suc n} {suc m} (odd p1) (odd p2) = subst Even (cong suc (lem-plus-s n m) ) (ev-s (lem-plus-of-evens p1 p2))
lem-plus-of-odds {m = zero} _ ()
lem-plus-of-odds {n = zero} () _

lem-twice-is-even : ∀ n → Even (n + n)
lem-twice-is-even zero = ev-0
lem-twice-is-even (suc n) = subst Even (cong suc (lem-plus-s n n)) (ev-s (lem-twice-is-even n))

lem-mult-of-evens-l : ∀ {n m} → Even n → Even (n * m)
lem-mult-of-evens-l {.zero} ev-0 = ev-0
lem-mult-of-evens-l {suc (suc n)} {m} (ev-s y) = subst Even (lem-plus-assoc m m (n * m)) (lem-plus-of-evens (lem-twice-is-even m) (lem-mult-of-evens-l y))

lem-mult-of-odds : ∀ {n m} → Odd n → Odd m → Odd (n * m)
lem-mult-of-odds {suc n} {suc m} (odd y) (odd y') = odd (lem-plus-of-evens y' (lem-mult-of-evens-l y))
lem-mult-of-odds {zero} () _
lem-mult-of-odds {n} {zero} _ ()

lem-square-of-evens : ∀ {n} → Even n → Even (n * n)
lem-square-of-evens p = lem-mult-of-evens-l p

lem-square-of-odds : ∀ {n} → Odd n → Odd (n * n)
lem-square-of-odds p = lem-mult-of-odds p p

lem-odd-or-even : ∀ n → Even n ⊎ Odd n
lem-odd-or-even zero = inj₁ ev-0
lem-odd-or-even (suc n) with lem-odd-or-even n
...                            | inj₁ p = inj₂ (odd p)
lem-odd-or-even (suc .(suc n)) | inj₂ (odd {n} y) = inj₁ (ev-s y)

{- BASE parity lem-plus-of-evens lem-plus-of-odds lem-twice-is-even 
        lem-mult-of-odds lem-mult-of-evens-l lem-square-of-odds lem-odd-or-even -}

---------------------
--  A parity view  --
---------------------

data Parity : ℕ → Set where
  odd  : (k : ℕ) → Parity (1 + k * 2)
  even : (k : ℕ) → Parity (k * 2)

getParity : (n : ℕ) → Parity n
getParity zero = even zero
getParity (suc n) with getParity n
getParity (suc .(suc (k * 2))) |  odd k = even (suc k)
getParity (suc .(k * 2))       | even k = odd k

----------------------------------
--  Properties of (my) compare  --
----------------------------------

{- 
   My own comparing function and result datatype. 
   The compare function from Data.Nat produces a lot of noise.
-}
  
data Ord : Set where
 LT EQ GT : Ord

compare : ℕ → ℕ → Ord
compare zero zero    = EQ
compare zero (suc n) = LT
compare (suc n) zero = GT
compare (suc n) (suc n') = compare n n'

EQ≠LT : EQ ≢ LT
EQ≠LT ()

EQ≠GT : EQ ≢ GT
EQ≠GT ()

LT≠EQ : LT ≢ EQ
LT≠EQ ()

LT≠GT : LT ≢ GT
LT≠GT ()

GT≠LT : GT ≢ LT
GT≠LT ()

GT≠EQ : GT ≢ EQ
GT≠EQ ()

lem-compare-refl : (n : ℕ) → compare n n ≡ EQ
lem-compare-refl zero    = refl
lem-compare-refl (suc n) = lem-compare-refl n

lem-compare-swap : ∀ {m n} → compare m n ≡ GT → compare n m ≡ LT
lem-compare-swap {zero} {zero} ()
lem-compare-swap {zero} {suc n} ()
lem-compare-swap {suc m} {zero} p = refl
lem-compare-swap {suc m} {suc n} p = lem-compare-swap {m = m} p

lem-compare-trans-lt : ∀ {m n l} → compare m n ≡ LT → compare n l ≡ LT → compare m l ≡ LT
lem-compare-trans-lt {zero} {zero} {l} mn nl = nl
lem-compare-trans-lt {(suc n)} {zero} {l} () nl
lem-compare-trans-lt {m} {(suc n)} {zero} mn ()
lem-compare-trans-lt {zero} {(suc n)} {(suc n')} mn nl = refl
lem-compare-trans-lt {(suc m)} {(suc n')} {(suc n0)} mn nl = lem-compare-trans-lt {m = m} mn nl

lem-compare-eq : ∀ {n m} → compare n m ≡ EQ → n ≡ m
lem-compare-eq {zero} {zero} p = refl
lem-compare-eq {zero} {suc n} ()
lem-compare-eq {suc n} {zero} ()
lem-compare-eq {suc n} {suc n'} p = cong suc (lem-compare-eq p)

{- BASE compare EQ≠GT EQ≠LT GT≠EQ GT≠LT LT≠GT LT≠EQ lem-compare-refl lem-compare-swap lem-compare-trans-lt lem-compare-eq -}

-----------------------------
--  Properties of ⊔ and <  --
-----------------------------

lem-≤-suc : ∀ (n : ℕ) → n ≤ suc n
lem-≤-suc zero = z≤n
lem-≤-suc (suc n) = s≤s (lem-≤-suc n)

lem-≤-refl : Reflexive _≤_
lem-≤-refl = Poset.refl (DecTotalOrder.poset decTotalOrder)

lem-≤-trans : Transitive _≤_
lem-≤-trans = Poset.trans (DecTotalOrder.poset decTotalOrder)

lem-<-trans : Transitive _<_
lem-<-trans {j = suc n} (s≤s m≤n) (s≤s n≤k) = s≤s (lem-≤-trans (lem-≤-trans m≤n (lem-≤-suc n)) n≤k)
lem-<-trans {j = zero} () p2

{- BASE arith lem-≤-refl lem-≤-trans lem-≤-suc lem-<-trans -}

lem-⊔ : ∀ (n m : ℕ) → n ⊔ m ≡ n ⊎ n ⊔ m ≡ m
lem-⊔ zero m = inj₂ refl
lem-⊔ (suc n) zero = inj₁ refl
lem-⊔ (suc n) (suc n') with lem-⊔ n n' 
lem-⊔ (suc n) (suc n') | inj₁ x = inj₁ (cong suc x)
lem-⊔ (suc n) (suc n') | inj₂ y = inj₂ (cong suc y)

lem-≤-l+ : ∀ (m p q : ℕ) → m ≤ q → m ≤ p + q
lem-≤-l+ m zero q pr = pr
lem-≤-l+ .0 (suc n) q z≤n = z≤n
lem-≤-l+ .(suc m) (suc n) .(suc n') (s≤s {m} {n'} m≤n) = s≤s (≤-cong (lem-≤-l+ m (suc n) n' m≤n) (lem-plus-s n n')) where
  ≤-cong : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
  ≤-cong x<=y refl = x<=y

lem-≤-+r : ∀ (m p q : ℕ) → m ≤ q → m ≤ q + p
lem-≤-+r .0 n q z≤n = z≤n
lem-≤-+r .(suc m) zero .(suc n) (s≤s {m} {n} m≤n) = s≤s (lem-≤-+r m zero n m≤n)
lem-≤-+r .(suc m) (suc n) .(suc n') (s≤s {m} {n'} m≤n) = s≤s (lem-≤-+r m (suc n) n' m≤n)

lem-≤-cong2 : ∀ {n m p q} → n ≤ p → m ≤ q → n + m ≤ p + q
lem-≤-cong2 {.zero} {m} {p} {q} z≤n x' = lem-≤-l+ m p q x'
lem-≤-cong2 (s≤s m≤n) x' = s≤s (lem-≤-cong2 m≤n x')

lem-<-cong : ∀ {n m p q} → n < p → m < q → (n ⊔ m) < p + q
lem-<-cong {n} {m} p1 p2 with lem-⊔ n m 
lem-<-cong {n} {m} {p} {q} p1 p2 | inj₁ x rewrite x = lem-≤-+r (suc n) q p p1
lem-<-cong {n} {m} {p} {q} p1 p2 | inj₂ y rewrite y = lem-≤-l+ (suc m) p q p2

{- BASE arith lem-⊔ lem-≤-l+ lem-≤-+r lem-≤-cong2 lem-<-cong -}

------------------------------------------
--  Converting between < and ≤ (and ≡)  --
------------------------------------------

lem-≤-cases : ∀ (n m : ℕ) → n ≤ m → n < m ⊎ n ≡ m
lem-≤-cases .0 zero z≤n = inj₂ refl
lem-≤-cases .0 (suc n) z≤n = inj₁ (s≤s z≤n)
lem-≤-cases .(suc m) .(suc n) (s≤s {m} {n} m≤n) with lem-≤-cases m n m≤n
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ r = inj₂ (cong suc r)

-- bad naming, but I have no better idea
lem-≤-cases-ext : ∀ (n m : ℕ) → n ≤ m → n ≢ m → suc n ≤ m
lem-≤-cases-ext n m n≤m n≡m with lem-≤-cases n m n≤m
lem-≤-cases-ext n m n≤m n≡m | inj₁ n<m = n<m
lem-≤-cases-ext n m n≤m n≡m | inj₂ n=m = ⊥-elim (n≡m n=m)

lem-suc-n-n-impossible : ∀ {n : ℕ} → ¬ (suc n ≤ n)
lem-suc-n-n-impossible (s≤s m≤n) = lem-suc-n-n-impossible m≤n

lem-both-≤-<-impossible : ∀ {n m : ℕ} → n ≤ m → m < n -> ⊥
lem-both-≤-<-impossible {n} {m} x x' = lem-suc-n-n-impossible (lem-≤-trans x' x)

lem-≤-eq : ∀ {n n' m : ℕ} → n ≡ n' → n ≤ m → n' ≤ m
lem-≤-eq refl p = p

lem-≤-eq-refl : ∀ {n m} → n ≡ m → n ≤ m
lem-≤-eq-refl refl = lem-≤-refl

{- BASE arith lem-≤-cases lem-≤-cases-ext lem-suc-n-n-impossible lem-≤-eq lem-≤-eq-refl -}

-------------------------
--  Properties of _≟_  --
-------------------------

lem-≟-refl : ∀ (n : ℕ) → (n ≟ n) ≡ yes refl
lem-≟-refl zero = refl
lem-≟-refl (suc n) rewrite lem-≟-refl n = refl

lem-less-means-no : ∀ (n m : ℕ) → (n < m) → (p : n ≡ m) → ⊥
lem-less-means-no .(suc n) .(suc n) (s≤s {.(suc n)} {n} m≤n) refl = lem-less-means-no n n m≤n refl

{- BASE arith lem-less-means-no -}

---------------------------------------
--  Proof irrelevance for orderings  --
---------------------------------------

lem-≤-irrelv : ∀ {n k : ℕ} → {p1 : n ≤ k} → {p2 : n ≤ k} → p1 ≡ p2
lem-≤-irrelv {p1 = z≤n} {p2 = z≤n} = refl
lem-≤-irrelv {p1 = s≤s m≤n} {p2 = s≤s m≤n'} rewrite lem-≤-irrelv {p1 = m≤n} {p2 = m≤n'} = refl

lem-<-irrelv : ∀ {n k : ℕ} → {p1 : n < k} → {p2 : n < k} → p1 ≡ p2
lem-<-irrelv = lem-≤-irrelv

{- BASE irrelv lem-≤-irrelv lem-<-irrelv -}

-------------------------
--  Safe substraction  --
-------------------------

safeMinus : (m n : ℕ) → m ≤ n → ∃ (λ (k : ℕ) → n ≡ m + k)
safeMinus .0 n z≤n = n , refl
safeMinus .(suc m) .(suc n) (s≤s {m} {n} m≤n) with safeMinus m n m≤n
safeMinus .(suc m) .(suc n) (s≤s {m} {n} m≤n) | k , n≡m+k = k , cong suc n≡m+k

-----------------------------------------
--  Properties of unsafe substraction  --
-----------------------------------------

lem-minus-positive : ∀ (n k : ℕ) → n < k → 1 ≤ k ∸ n
lem-minus-positive .0 .(suc n) (s≤s {.0} {n} z≤n) = s≤s z≤n
lem-minus-positive .(suc m) .(suc (suc n)) (s≤s (s≤s {m} {n} m≤n)) = lem-minus-positive m (suc n) (s≤s m≤n) 

lem-minus-eq : ∀ (n k : ℕ) → k ≤ n → suc (n ∸ k) ≡ (suc n ∸ k)
lem-minus-eq n .0 z≤n = refl
lem-minus-eq .(suc n) .(suc m) (s≤s {m} {n} m≤n) = lem-minus-eq n m m≤n

{- BASE arith lem-minus-positive lem-minus-eq -}
{- BASE minus lem-minus-positive lem-minus-eq -}

-------------------------------------
--  ≤ and ≤' (copied from stdlib)  --
-------------------------------------

-- Converting between ≤ and ≤′

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

≤′⇒≤ : _≤′_ ⇒ _≤_
≤′⇒≤ ≤′-refl        = lem-≤-refl
≤′⇒≤ (≤′-step m≤′n) = ≤-step (≤′⇒≤ m≤′n)

z≤′n : ∀ {n} → zero ≤′ n
z≤′n {zero}  = ≤′-refl
z≤′n {suc n} = ≤′-step z≤′n

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl        = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤⇒≤′ : _≤_ ⇒ _≤′_
≤⇒≤′ z≤n       = z≤′n
≤⇒≤′ (s≤s m≤n) = s≤′s (≤⇒≤′ m≤n)

<⇒<′ : _<_ ⇒ _<′_
<⇒<′ = ≤⇒≤′

