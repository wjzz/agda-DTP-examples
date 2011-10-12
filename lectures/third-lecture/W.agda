module W where


-- Intro ------------------------------------------------------------------

open import Data.Product
open import Data.Fin
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Function
open import Universe
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

postulate
  funcExtDep : {A : Set} {B : A -> Set} -> (f g : (a : A) -> B a)
            -> ((x : A) -> f x ≡ g x) -> f ≡ g

funcExt : {A B : Set} (f g : A -> B) -> ((x : A) -> f x ≡ g x) -> f ≡ g
funcExt = funcExtDep


noFin0 : {Y : Set} -> Fin 0 -> Y
noFin0 ()

onlyOneFin1 : (a b : Fin 1) -> a ≡ b
onlyOneFin1 zero zero = refl
onlyOneFin1 (suc k) b = noFin0 k
onlyOneFin1 b (suc k) = noFin0 k

oneEmptyFunc : {Y : Set} (f g : Fin 0 -> Y) -> f ≡ g
oneEmptyFunc f g = funcExt f g H
 where
   H : ( x : Fin 0 ) -> f x ≡ g x
   H ()

-- W-type -----------------------------------------------------------------

data W (A : Set) (B : A -> Set) : Set where
  sup : (a : A) -> ( B a -> W A B ) -> W A B

-- elimination (induction principle)

Wrec : -- W-type parameters
    {A : Set} {B : A -> Set} 
    -- property
    {C : W A B -> Set}
    -- proof: C (sup x y) holds if C holds for any predecessor of (sup x y)
  -> ( (x : A) (y : B x -> W A B) -> (z : (v : B x) -> C (y v)) -> C (sup x y))
    -- result: C holds for any c
  -> (c : W A B) -> C c

-- like in Martin-Lof's book
Wrec {A} {B} {C} H (sup a b) = H a b z
 where
   z = λ v -> Wrec {A} {B} {C} H (b v)

-- simplification ;)
Wsrec : {A : Set} {B : A -> Set} {C : Set}
  -> ( (x : A) -> (B x -> W A B) -> (z : B x -> C ) -> C)
  -> W A B -> C

Wsrec {A} {B} {C} = Wrec {C = λ _ -> C}

-- casting to Σ-type
WSigma : {A : Set} {B : A -> Set} -> W A B -> Σ A (λ a -> B a -> W A B)
WSigma (sup a b) = a , b

-- theorem:
-- W A B is inhabited if there exists a:A such that B a is not inhabited

Wnonempty : ∀ {A : Set} {B : A -> Set}
         -> ∃ (λ x -> ¬ B x)
         -> ∃ (λ (x : W A B) -> ⊤ )

Wnonempty {A} {B} H = witness , tt
 where
   b : B (proj₁ H) -> W A B
   b = ⊥-elim ∘ proj₂ H

   witness : W A B
   witness = sup (proj₁ H) b

-- Natural numbers --------------------------------------------------------

-- indexes
nA = Fin 2

-- nodes
nB : Fin 2 -> Set
nB zero    = Fin 0
nB (suc _) = Fin 1

altN : Set
altN = W nA nB

altZero : altN
altZero = sup a b
 where
   a = zero
   b : nB zero -> altN
   b ()

altSucc : altN -> altN
altSucc n = sup a b
 where
   a = suc zero
   b : nB (suc zero) -> altN
   b k = n


altZeroAny : {P : altN -> Set}
          -> P altZero -> (y : Fin 0 -> altN) -> P (sup zero y)
altZeroAny {P} H y = subst (λ p -> P (sup zero p)) (oneEmptyFunc f0 y) H
 where
   f0 = proj₂ (WSigma altZero)



isZero : altN -> Bool
isZero = Wsrec f
 where
   f : (x : nA) -> (nB x -> W nA nB) -> (nB x -> Bool) -> Bool
   f zero _ _    = true
   f (suc k) _ _ = false

fromN : ℕ -> altN
fromN 0       = altZero
fromN (suc n) = altSucc (fromN n)

toN : altN -> ℕ
toN = Wsrec f
 where
   f : (x : nA) -> (nB x -> W nA nB) -> (nB x -> ℕ) -> ℕ
   f zero _ _    = 0
   f (suc k) y z = suc (z zero)


-- recursion

altNrec : {P : altN -> Set}
      -> P altZero
      -> ( (n : altN) -> P n -> P (altSucc n) )
      -> (n : altN) -> P n

altNrec {P} HP0 HPSn = Wrec {C = P} H'
 where

   H' : (x : Fin 2) (y : nB x -> W nA nB) -> (z : (v : nB x) -> P (y v))
     -> P (sup x y)

   H' zero    y _ = altZeroAny {P = P} HP0 y
   H' (suc k) y z = subst (λ p -> P (sup (suc k) p)) (sym Heq) HSn
     where
       n : altN
       n = y k

       HSn : P (sup (suc k) (const n))
       HSn = subst (λ p -> P (sup (suc p) (const n))) (onlyOneFin1 zero k) HSn'
         where
           HSn' : P (sup (suc zero) (const n))
           HSn' = HPSn n (z k)

       Heq : y ≡ const n
       Heq = funcExt y (const n) allx
         where
           allx : (x : Fin 1) -> y x ≡ const n x
           allx x = subst (λ p -> y p ≡ const n x) (onlyOneFin1 k x) refl

-- simplification

altNsrec : {P : Set}
        -> P
        -> (altN -> P -> P)
        -> altN -> P

altNsrec = altNrec 



-- Problems ---------------------------------------------------------------

plus : altN -> altN -> altN
plus n m = altNsrec m (λ _ -> altSucc) n

w-plus : altN -> altN -> altN
w-plus n m = Wsrec f n
 where
   f : (x : nA) -> (nB x -> altN) -> (nB x -> altN) -> altN
   f zero _ _    = m
   f (suc k) _ z = altSucc (z k)


ta = fromN 2
tb = fromN 1

test   = toN (plus ta tb)
w-test = toN (w-plus ta tb)



