---------------------------------------------------------------------------
--   based on Adam Chlipala's book
-- (not finished)
---------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Regexp where

-- open import Data.String
open import Data.Char
open import Data.List  --  renaming (_++_ to append)
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Nat
open import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- String representation
STR : Set
STR = List Char

---------------------------------------------------------------------------
-- Helpers
---------------------------------------------------------------------------

_<?_ : Decidable _<_
n <? m = suc n ≤? m

neg< : {n m : ℕ} -> ¬ (n < m) -> m ≤ n
neg< = _

neg<but<S : {n m : ℕ} -> ¬ (n < m) -> (n < suc m) -> n ≡ m
neg<but<S {n} {m} H< H<= = f (Data.Nat._≟_ n m)
 where
   f : Dec (n ≡ m) ->  n ≡ m
   f (yes H) = H
   f (no H) = _


Hlisteq : {A : Set} -> {x y : A} -> {xs ys : List A}
       -> (x ∷ xs ≡ y ∷ ys)
       -> (x ≡ y) × (xs ≡ ys)
Hlisteq = _

Htakedrop : {A : Set} -> (n : ℕ)
         -> (xs : List A) -> (take n xs) ++ (drop n xs) ≡ xs

Htakedrop 0 _
  = refl

Htakedrop (suc k) []
  = refl

Htakedrop (suc k) (x ∷ xs)
  = subst (λ p -> x ∷ p ≡ x ∷ xs) (sym $ Htakedrop k xs) refl

-- decide if two strings are equal
_===_ : (xs : List Char) -> (ys : List Char) -> Dec (xs ≡ ys)
[]       === []       = yes refl
[]       === (_ ∷ _)  = no λ()
(_ ∷ _)  === []       = no λ()
(x ∷ xs) === (y ∷ ys) = step1 (Data.Char._≟_  x y)
 where
   step2 : Dec (xs ≡ ys) -> Dec (x ∷ xs ≡ x ∷ ys)
   step2 (yes H) = subst (λ p -> Dec (x ∷ xs ≡ x ∷ p)) H (yes refl)
   step2 (no  H) = no (H ∘ proj₂ ∘ Hlisteq)

   step1 : Dec (x ≡ y) -> Dec (x ∷ xs ≡ y ∷ ys)
   step1 (no  H) = no (H ∘ proj₁ ∘ Hlisteq)
   step1 (yes H) = subst (λ p -> Dec (x ∷ xs ≡ p ∷ ys)) H (step2 (xs === ys))


---------------------------------------------------------------------------
-- Regexp constraints and their semantic
---------------------------------------------------------------------------
-- I prefer to have data type for constraits because
--  a> as beginner I have troubles with universe polymorphism :)
--  b> it is easier to verify if constraints and their semantics are correct

data RegexpConstr : Set where
  rcEqualTo : STR -> RegexpConstr
  rcSeq     : RegexpConstr -> RegexpConstr -> RegexpConstr
  rcOr      : RegexpConstr -> RegexpConstr -> RegexpConstr
  rcIter    : RegexpConstr -> RegexpConstr

data RegexpStar (P : STR -> Set) : STR -> Set where
  rsEmpty   : RegexpStar P []
  rsIter    : (s1 s2 : STR) -> P s1 -> RegexpStar P s2
           -> RegexpStar P (s1 ++ s2)

mutual 
  rcSeqCheck : RegexpConstr -> RegexpConstr -> STR -> STR -> STR -> Set
  rcSeqCheck c1 c2 s s1 s2 = s ≡ s1 ++ s2 × rcCheck c1 s1 × rcCheck c2 s2

  rcCheck : RegexpConstr -> STR -> Set

  rcCheck (rcEqualTo s') s
    = s ≡ s'

  rcCheck (rcSeq c1 c2) s
    = ∃ (λ s1 -> ∃ (λ s2 -> rcSeqCheck c1 c2 s s1 s2 ))

  rcCheck (rcOr c1 c2) s
    = rcCheck c1 s ⊎ rcCheck c2 s

  rcCheck (rcIter c1) s
    = RegexpStar (rcCheck c1) s

---------------------------------------------------------------------------
-- Regexp representation
---------------------------------------------------------------------------

data Regexp : RegexpConstr -> Set where

  reEmpty  : Regexp (rcEqualTo [])

  reChar   : ( ch : Char )
          -> Regexp (rcEqualTo [ ch ])

  reConcat : {P1 P2 : RegexpConstr}
          -> (R1 : Regexp P1)
          -> (R2 : Regexp P2)
          -> Regexp (rcSeq P1 P2)

  reOr     : {P1 P2 : RegexpConstr}
          -> (R1 : Regexp P1)
          -> (R2 : Regexp P2)
          -> Regexp (rcOr P1 P2)

  reStar   : {P1 : RegexpConstr }
          -> (R1 : Regexp P1)
          -> Regexp (rcIter P1)

---------------------------------------------------------------------------
-- Matcher: string comparision
---------------------------------------------------------------------------

re_equal : (src : STR) -> (sin : STR) -> Dec (rcCheck (rcEqualTo src) sin)
re_equal src sin = sin === src

---------------------------------------------------------------------------
-- Matcher: union of expressions
---------------------------------------------------------------------------

re_or : {c1 c2 : RegexpConstr} -> (sin : STR)
     -> ( (s : STR) -> Dec (rcCheck c1 s)) -> ( (s : STR) -> Dec (rcCheck c2 s))
     -> Dec (rcCheck (rcOr c1 c2) sin)
re_or {c1} {c2} sin l r = step1 (l sin)
 where

   -- match second regular expression
   step2 : ¬ (rcCheck c1 sin) -> Dec (rcCheck c2 sin)
       -> Dec (rcCheck (rcOr c1 c2) sin)
     -- yes, transform proof R into (L ∨ R) and return
   step2 _   (yes H) = yes ∘ inj₂ $ H
     -- no, construct proof that ¬(L ∨ R) and return
   step2 Hc1 (no H)  = no (Data.Sum.[_,_] Hc1 H)

   -- check if sin matches first regexp
   step1 : Dec (rcCheck c1 sin) -> Dec (rcCheck (rcOr c1 c2) sin)
     -- yes, transform proof L into (L ∨ R) and return
   step1 (yes H) = yes ∘ inj₁ $ H
     -- no, remember proof that sin doesn't match with regexp and go to step2
   step1 (no H)  = step2 H (r sin)


---------------------------------------------------------------------------
-- Matcher: sequence of expressions
---------------------------------------------------------------------------

re_seq : {c1 c2 : RegexpConstr} -> (sin : STR)
      -> ( (s : STR) -> Dec (rcCheck c1 s)) -> ( (s : STR) -> Dec (rcCheck c2 s))
      -> Dec (rcCheck (rcSeq c1 c2) sin)
re_seq {c1} {c2} sin m1 m2 = step1
  where

    -- iterate over string
    split : (n : ℕ) -> (xs : List Char) -> Dec (rcCheck (rcSeq c1 c2) xs)
    split n xs = search 0 (z≤n) Hind0
      where
        -- length of String
        slength : STR -> ℕ
        slength = length

        -- hypothesis for search 0
        Hind0  : (s' : STR) -> slength s' < 0 -> ¬ rcCheck (rcSeq c1 c2) s'
        Hind0 s' H0n _ = bad H0n
          where
            bad : ¬ slength s' < 0
            bad ()

        -- check if (take s xs), (drop s xs) is correct sequence
        search : (s : ℕ) -> s ≤ n
              -> ( (s' : STR) -> slength s' < s -> ¬ rcCheck (rcSeq c1 c2) s')
              -> Dec (rcCheck (rcSeq c1 c2) xs)
        search s Hsn Hind = try (m1 s1) (m2 s2)
          where
            s1  = take s xs
            s2  = drop s xs

            Heq : xs ≡ s1 ++ s2
            Heq = sym (Htakedrop s xs)

            try : Dec (rcCheck c1 s1) -> Dec (rcCheck c2 s2)
               -> Dec (rcCheck (rcSeq c1 c2) xs)

            try (yes H1) (yes H2) = yes (s1 , (s2 , (Heq , ( H1 , H2 ) )))
            try _ _ = _

            Hind' : ¬ (rcSeqCheck c1 c2 xs s1 s2)
                 -> (s' : STR) -> slength s' < suc s
                 -> ¬ rcCheck (rcSeq c1 c2) s'
            Hind' Hxs s' Hs' = check (slength s' <? s)
              where
                check : Dec (slength s' < s) -> ¬ (rcCheck (rcSeq c1 c2) s')
                check (yes Hs'') = Hind s' Hs''
                check (no H)     = _

            end? : Dec (s ≡ n) -> ¬ rcSeqCheck c1 c2 xs s1 s2
                -> Dec (rcCheck (rcSeq c1 c2) xs)
            end? (no _)  Hxs = _
            end? (yes _) Hxs = _
      

-- rcSeqCheck

    -- get s1 s2 such that s = s1 ++ s2 and s1,s2 is correct sequence
    -- or proof that sequence doesn't exist
    step1 = split (length xs) xs
      where
        xs = sin


---------------------------------------------------------------------------
-- Matcher: Kleene's closure
---------------------------------------------------------------------------

re_iter : {c1 : RegexpConstr} -> (sin : STR)
       -> ( (s : STR) -> Dec (rcCheck c1 s))
       -> Dec (rcCheck (rcIter c1) sin)
-- match string with (r)* regexp
re_iter {c1} sin m = step1 ([] === sin)
 where
   -- first, match string with empty string
   step1 : Dec (rcCheck (rcEqualTo sin) []) -> Dec (rcCheck (rcIter c1) sin)
     -- matched, return proof that "" matches (r)*
   step1 (yes H) = subst (λ p -> Dec (rcCheck (rcIter c1) p)) H (yes (rsEmpty))
   step1 (no H)  = _

---------------------------------------------------------------------------
-- Matcher
---------------------------------------------------------------------------

match : {rc : RegexpConstr} -> Regexp rc -> (sin : STR) -> Dec (rcCheck rc sin)
match (reChar ch) sin
  = re_equal [ ch ] sin

match reEmpty sin
  = re_equal [] sin

match {rcOr c1 c2} (reOr r1 r2) sin
  = re_or {c1} {c2} sin (match r1) (match r2)

match {rcSeq c1 c2} (reConcat r1 r2) sin
  = re_seq {c1} {c2} sin (match r1) (match r2)

match {rcIter c1} (reStar r1) sin
  = re_iter {c1} sin (match r1)
