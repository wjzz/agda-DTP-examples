-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-20
-- @tags   : Agda ; Unification; DTP
-- @short  : The unification algorithm using structural recursion from McBride's paper

module Unification where

-- Key part from the paper:
-- "Dependent type systems give us a much richer language in which to describe data.
-- In particular, we can stratify the type of terms into a family of types, Term n ,
-- representing terms over a set of n variables. This paper presents a first-order uni-
-- cation algorithm which is structurally recursive on this n :"

------------------------------------------------
--  Some preliminary examples from the paper  --
------------------------------------------------

open import Data.Nat
open import Data.Fin hiding (_+_)

empty : ∀ {T : Set} → Fin 0 → T
empty ()

-- structural induction

ack : ℕ → ℕ → ℕ
ack zero     m      = suc m
ack (suc n)  zero   = ack n 1
ack (suc n) (suc m) = ack n (ack (suc n) m)

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- A note on structural recursion:
-- "A dependent type system such as Lego's, which only provides higher-order primi-
-- tive recursion, can nonetheless support all the programs de nable by pattern match-
-- ing and structural recursion in the above sense. The full translation procedure is
-- given in my thesis (McBride, 1999), but the basic idea is to use primitive recursion
-- to build an auxiliary data structure memoizing all `prior' outputs for each input|
-- the original function's recursive calls are replaced by look-up operations on this
-- structure."

-- On the main trick:

-- "Dependent types add more than just detail to the class of structurally recursive
-- function de nitions. An inductive family indexed by a datatype has two notions of
-- structural recursion: the constructors of the index type give one, and the construc-
-- tors of the family itself give another. The two may have quite di erent behaviours,
-- and they may be combined by nesting. Inductive families thus allow us to avoid
-- general recursion in situations where we can see how to turn hidden recursive struc-
-- ture into the explicit inductive structure of an index type. That is how we shall
-- write first-order uni cation by structural recursion."

-------------
--  Terms  --
-------------

open import Data.Empty
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- terms with at most n variables

data Term : ℕ → Set where
  var  : {n : ℕ} → (i : Fin n) → Term n
  leaf : {n : ℕ} → Term n
  fork : {n : ℕ} → (s t : Term n) → Term n

-- a simple algebra of substitutions

rename : {n m : ℕ} → (Fin m → Fin n) → (Fin m → Term n)
rename f = var ∘ f

substitution : {n m : ℕ} → (Fin n → Term m) → Term n → Term m
substitution f (var i)    = f i
substitution f leaf       = leaf
substitution f (fork s t) = fork (substitution f s) (substitution f t)

-- var is monadic return

-- composition of substitutions

bind : {n m l : ℕ} → (Fin m → Term n) → (Fin l → Term m) → (Fin l → Term n)
bind f g = substitution f ∘ g

-- extensional equality on substitutions

_==_ : {m n : ℕ} → (f g : Fin m → Term n) → Set
f == g = ∀ {x} → f x ≡ g x

-- embedding x 

thin : {n : ℕ} → (x : Fin (suc n)) → (y : Fin n) → Fin (suc n)
thin zero y          = suc y
thin (suc x) zero    = zero
thin (suc x) (suc y) = suc (thin x y)

-- properties of thin

strip-suc : ∀ {n : ℕ} → (x y : Fin n) → _≡_ {A = Fin (suc n)} (suc x) (suc y) → x ≡ y
strip-suc .y y refl = refl

thin-inv : {n : ℕ} → (x : Fin (suc n)) (y z : Fin n) → thin x y ≡ thin x z → y ≡ z
thin-inv zero .z z refl = refl
thin-inv (suc i) zero zero p = refl
thin-inv (suc i) zero (suc i') ()
thin-inv (suc i) (suc i') zero ()
thin-inv (suc i) (suc i') (suc i0) p = cong suc (thin-inv i i' i0 (strip-suc _ _ p))

thin-diff : {n : ℕ} → (x : Fin (suc n)) (y : Fin n) → thin x y ≢ x
thin-diff zero y ()
thin-diff (suc i) zero ()
thin-diff (suc i) (suc i') eq = thin-diff i i' (strip-suc (thin i i') i eq)

thin-others : {n : ℕ} → (x y : Fin (suc n)) → x ≢ y → Σ[ y' ∶ Fin n ](thin x y' ≡ y)
thin-others zero zero p = ⊥-elim (p refl)
thin-others zero (suc i) p = i , refl
thin-others {zero} (suc ()) zero p
thin-others {suc n} (suc i) zero p = zero , refl
thin-others {zero} (suc ()) (suc i') p
thin-others {suc n} (suc i) (suc i') p with thin-others i i' (λ x → p (cong suc x))
... | y' , proof = suc y' , cong suc proof

-- an inversion to thin

open import Data.Maybe
open import Category.Functor
open RawFunctor functor

thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick zero zero               = nothing
thick zero (suc j)            = just j
thick {zero} (suc ()) y
thick {suc n} (suc i) zero    = just zero
thick {suc n} (suc i) (suc j) = suc <$> thick i j

open import Data.Sum
open import Data.Fin.Props renaming (_≟_ to _≟Fin_)
open import Relation.Nullary

thick-inv : ∀ {n} (x y : Fin (suc n)) → (x ≡ y × thick x y ≡ nothing) ⊎ (Σ[ y' ∶ Fin n ](thin x y' ≡ y × thick x y ≡ just y'))
thick-inv x y with x ≟Fin y
thick-inv zero zero | yes p = inj₁ (refl , refl)
thick-inv zero (suc i) | yes ()
thick-inv (suc i) zero | yes ()
thick-inv {zero} (suc ()) (suc i') | yes p
thick-inv {suc n }(suc i) (suc i') | yes p with thick-inv i i'
... | inj₁ (eq , y) rewrite y = inj₁ (p , refl)
... | inj₂ y = {!!}
thick-inv x y | no ¬p = {!!}

open import Category.Monad
open RawMonad monad using (_>>=_; return)


-- If check x return nothing, then x occurs in t
-- Otherwise we get a term with one slot less than the original one

check : {n : ℕ} → (x : Fin (suc n)) →  (t : Term (suc n)) → Maybe (Term n)
check x (var i) = var <$> thick x i
check x leaf = just leaf
check x (fork s t) = check x s >>= λ s' → 
                     check x t >>= λ t' → 
                     return (fork s' t')
                     -- TODO: rewrite it using applicative components

-- the unifier for the 'no occurs check' case

_for_ : {n : ℕ} → (t : Term n) → (x : Fin (suc n)) → Fin (suc n) → Term n
(t for x) y with thick x y
... | just y' = var y'
... | nothing = t

