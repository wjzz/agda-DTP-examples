{-# OPTIONS --universe-polymorphism #-}

module ListUtils where

open import Data.Empty
open import Data.Nat
open import NatUtils
open import Data.List
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

{- BASE global ⊥-elim -}

-------------------------------------------------
--  Properties of the standard list functions  --
-------------------------------------------------

-- lemma for pattern matching/rewrite failure

lem-length-eq :  ∀ {A : Set} → {l1 l2 : List A} → l1 ≡ l2 → length l1 ≡ length l2
lem-length-eq refl = refl

{- length properties -}

lem-length-app : ∀ {A : Set} → (l1 l2 : List A) → length (l1 ++ l2) ≡ length l1 + length l2
lem-length-app [] l2 = refl
lem-length-app (x ∷ xs) l2 = cong suc (lem-length-app xs l2)

lem-length-map : ∀ {A B : Set} (f : A → B) (l : List A) → length l ≡ length (Data.List.map f l)
lem-length-map f [] = refl
lem-length-map f (x ∷ xs) = cong suc (lem-length-map f xs)

{- BASE lists lem-length-app lem-length-map -}

{- ++ properties -}

lem-app-l-nil : ∀ {A : Set}(l : List A) → l ++ [] ≡ l
lem-app-l-nil [] = refl
lem-app-l-nil (x ∷ xs) = cong (λ l → x ∷ l) (lem-app-l-nil xs)

lem-app-assoc : ∀ {A : Set}(l1 l2 l3 : List A) → l1 ++ (l2 ++ l3) ≡ (l1 ++ l2) ++ l3
lem-app-assoc [] l2 l3 = refl
lem-app-assoc (x ∷ xs) l2 l3 = cong (λ l → x ∷ l) (lem-app-assoc xs l2 l3)

lem-app-map : {A B : Set}(f : A → B)(xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
lem-app-map f [] ys = refl
lem-app-map f (x ∷ xs) ys = cong (_∷_ (f x)) (lem-app-map f xs ys)

{- BASE lists lem-app-l-nil lem-app-assoc -}

{- frev properties (auxillary lemmas for reverse -}

-- a crucial function for proving anything about reverse, 
-- as reverse = frev []
frev : {A : Set} (l1 l2 : List A) → List A
frev = foldl (λ rev x → x ∷ rev)

lem-foldl-app : ∀ {A : Set}(l1 l2 l3 : List A) → frev (l3 ++ l1) l2 ≡ frev l3 l2 ++ l1
lem-foldl-app l1 [] l3 = refl
lem-foldl-app l1 (x ∷ xs) l3 = lem-foldl-app l1 xs (x ∷ l3)

lem-foldl-app-rev : ∀ {A : Set}(l1 l2 : List A) → frev l1 l2 ≡ reverse l2 ++ l1
lem-foldl-app-rev l1 l2 = lem-foldl-app l1 l2 []


{- reverse properties -}

lem-reverse-head : ∀ {A : Set} (x : A) (xs : List A) → reverse (x ∷ xs) ≡ reverse xs ++ (x ∷ [])
lem-reverse-head x xs = lem-foldl-app-rev (x ∷ []) xs

lem-reverse-len : ∀ {A : Set} → (l : List A) → length (reverse l) ≡ length l
lem-reverse-len [] = refl
lem-reverse-len (x ∷ xs) = begin 
                            length (reverse (x ∷ xs))             ≡⟨ cong length (lem-reverse-head x xs) ⟩
                            length (reverse xs ++ (x ∷ []))       ≡⟨ lem-length-app (reverse xs) (x ∷ []) ⟩ 
                            length (reverse xs) + length (x ∷ []) ≡⟨ sym (lem-plus-1-n (length (reverse xs))) ⟩ 
                            1 + length (reverse xs)               ≡⟨ cong suc (lem-reverse-len xs) ⟩ 
                            length (x ∷ xs) ∎

lem-reverse-app : ∀ {A : Set} → (l1 l2 : List A) → reverse (l1 ++ l2) ≡ reverse l2 ++ reverse l1
lem-reverse-app [] l2       = sym (lem-app-l-nil (reverse l2))
lem-reverse-app (x ∷ l1) l2 = begin 
                               reverse ((x ∷ l1) ++ l2)                ≡⟨ lem-reverse-head x (l1 ++ l2) ⟩ 
                               reverse (l1 ++ l2) ++ (x ∷ [])          ≡⟨ cong (λ l → l ++ (x ∷ [])) (lem-reverse-app l1 l2) ⟩ 
                               (reverse l2 ++ reverse l1) ++ (x ∷ [])  ≡⟨ sym (lem-app-assoc (reverse l2) (reverse l1) (x ∷ [])) ⟩ 
                                reverse l2 ++ (reverse l1 ++ (x ∷ [])) ≡⟨ cong (λ l → reverse l2 ++ l) (sym (lem-reverse-head x l1)) ⟩ 
                               (reverse l2 ++ reverse (x ∷ l1)) ∎ 

{- BASE lists lem-reverse-head lem-reverse-len lem-reverse-app -}

-------------------------------------------------
--  List membership relation and member query  --
-------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} : (a : A) → (xs : List A) → Set where
  ∈-take : {a : A}   {xs : List A} → a ∈ a ∷ xs
  ∈-drop : {a x : A} {xs : List A} → a ∈ xs → a ∈ x ∷ xs


_∉_ : {A : Set} (a : A)(l : List A) → Set
a ∉ l = ¬ (a ∈ l)


-- lemmas for situations where pattern matching doesn't work

lem-∈-len-nonzero : ∀ {A : Set} {a : A} {l : List A} → a ∈ l → 0 ≢ length l
lem-∈-len-nonzero {A} {a} {[]} () 0≡l
lem-∈-len-nonzero {A} {a} {x ∷ xs} a∈l ()

lem-∉-empty : ∀ {A : Set} → (a : A) → a ∉ []
lem-∉-empty a ()

lem-∈-eq-l : ∀ {A : Set} (a : A)(xs ys : List A) → xs ≡ ys → a ∈ xs → a ∈ ys
lem-∈-eq-l a xs .xs refl inn = inn 

lem-∈-eq : ∀ {A : Set} (a a' : A)(xs : List A) → a ≡ a' → a ∈ a' ∷ xs
lem-∈-eq .a' a' xs refl = ∈-take

lem-∉-neq-tail : ∀ {A : Set} (a a' : A)(xs : List A) → a ≢ a' → a ∉ xs → a ∉ (a' ∷ xs)
lem-∉-neq-tail .a' a' xs neq a∉xs (∈-take {.a'} {.xs}) = neq refl
lem-∉-neq-tail a a' xs neq a∉xs (∈-drop y) = a∉xs y

lem-∉-cons : ∀ {A : Set} (a a' : A)(xs : List A) → a ∉ (a' ∷ xs) → a ≢ a'
lem-∉-cons a a' xs x eq rewrite eq = x (∈-take)

{- BASE in lem-∈-len-nonzero lem-∈-eq lem-∉-neq-tail lem-∉-cons -}


-- extension lemmas

lem-∈-extend-l : ∀ {A : Set} (a : A)(xs ys : List A) → a ∈ xs → a ∈ ys ++ xs
lem-∈-extend-l a xs [] inn = inn
lem-∈-extend-l a xs (x ∷ xs') inn = ∈-drop (lem-∈-extend-l a xs xs' inn)

lem-∈-extend-r : ∀ {A : Set} (a : A)(xs ys : List A) → a ∈ xs → a ∈ xs ++ ys
lem-∈-extend-r a .(a ∷ xs) ys (∈-take {.a} {xs}) = ∈-take
lem-∈-extend-r a .(x ∷ xs) ys (∈-drop {.a} {x} {xs} y) = ∈-drop (lem-∈-extend-r a xs ys y)

-- ∉ and ++

lem-∉-app-l : ∀ {A : Set} (a : A)(xs ys : List A) → a ∉ (xs ++ ys) → a ∉ xs
lem-∉-app-l a [] ys p ()
lem-∉-app-l a (x ∷ xs) ys nin axs = nin (lem-∈-extend-r a (x ∷ xs) ys axs) 

lem-∉-app-r : ∀ {A : Set} (a : A)(xs ys : List A) → a ∉ (xs ++ ys) → a ∉ ys
lem-∉-app-r a xs ys nin ays = nin (lem-∈-extend-l a ys xs ays)

lem-∈-inside : ∀ {A : Set}(a : A) (xs ys : List A) → a ∈ xs ++ (a ∷ ys)
lem-∈-inside a [] ys = ∈-take
lem-∈-inside a (x ∷ xs) ys = ∈-drop (lem-∈-inside a xs ys)

lem-∈-neq : ∀ {A : Set}(a a' : A) (xs : List A) → a ≢ a' → a ∈ a' ∷ xs → a ∈ xs
lem-∈-neq .a' a' xs neq (∈-take {.a'} {.xs}) = ⊥-elim (neq refl)
lem-∈-neq a a' xs neq (∈-drop y) = y

lem-∈-app : ∀ {A : Set}(a : A) (xs ys : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → a ∈ xs ++ ys → a ∈ xs ⊎ a ∈ ys
lem-∈-app a [] ys cmp inn = inj₂ inn
lem-∈-app a (x ∷ xs) ys cmp inn with cmp a x
lem-∈-app a (x ∷ xs) ys cmp inn | yes p rewrite p = inj₁ ∈-take
lem-∈-app .x (x ∷ xs) ys cmp (∈-take {.x} {.(xs ++ ys)}) | no ¬p = inj₁ ∈-take
lem-∈-app a (x ∷ xs) ys cmp (∈-drop y) | no ¬p with lem-∈-app a xs ys cmp y
lem-∈-app a (x ∷ xs) ys cmp (∈-drop y) | no ¬p | inj₁ l = inj₁ (∈-drop l)
lem-∈-app a (x ∷ xs) ys cmp (∈-drop y) | no ¬p | inj₂ r = inj₂ r

lem-exists-find : ∀ {A : Set} (a : A)(l : List A) → a ∈ l → ∃₂ (λ (xs ys : List A) → l ≡ xs ++ [ a ] ++ ys)
lem-exists-find a .(a ∷ xs) (∈-take {.a} {xs}) = [] , xs , refl
lem-exists-find a .(x ∷ xs) (∈-drop {.a} {x} {xs} y) with lem-exists-find a xs y
lem-exists-find a .(x ∷ xs) (∈-drop {.a} {x} {xs} y) | ys , zs , p = x ∷ ys , zs , cong (_∷_ x) p

{- BASE in lem-∉-app-l lem-∉-app-r lem-∈-app lem-∈-neq lem-∈-inside lem-∈-extend-l lem-∈-extend-r lem-exists-find -}


-- decidable list membership

member : {A : Set} → (a : A) → (l : List A) → (eq : Decidable {A = A} _≡_) → Dec (a ∈ l)
member a [] eq = no (λ ())
member a (x ∷ xs) eq with inspect (eq a x)
member a (x ∷ xs) eq | yes p with-≡ eq' rewrite p = yes ∈-take
member a (x ∷ xs) eq | no ¬p with-≡ eq' with member a xs eq
member a (x ∷ xs) eq | no ¬p with-≡ eq'  | yes p = yes (∈-drop p)
member a (x ∷ xs) eq | no ¬p' with-≡ eq' | no ¬p = no (¬p ∘ lem-∈-neq a x xs ¬p')

---------------------------------------
--  A notion of set-like uniqueness  --
---------------------------------------

-- a list is distinct iff all moves are unique

data distinct {A : Set} : List A → Set where
  dist-nil  : distinct []
  dist-cons : {a : A}{l : List A} → (dist : distinct l) → a ∉ l → distinct (a ∷ l)

----------------------------------------
--  List subset relation and queries  --
----------------------------------------

infix 4 _⊂_

data _⊂_ {A : Set} : (l1 l2 : List A) → Set where
  nil  : {l : List A} → [] ⊂ l
  cons : {m : A} {ms l : List A} → ms ⊂ l → m ∈ l → m ∷ ms ⊂ l

lem-⊂-cons-inv-tail : ∀ {A : Set}(x : A)(xs ys : List A) → (x ∷ xs ⊂ ys) → xs ⊂ ys
lem-⊂-cons-inv-tail x xs ys (cons y y') = y  

lem-⊂-cons-inv-head : ∀ {A : Set}(x : A)(xs ys : List A) → (x ∷ xs ⊂ ys) → x ∈ ys
lem-⊂-cons-inv-head x xs ys (cons y y') = y'

lem-subset-alt : ∀ {A : Set}(x : A)(xs ys : List A) → (xs ⊂ ys) → x ∈ xs → x ∈ ys
lem-subset-alt x .(x ∷ xs) ys (cons y y') (∈-take {.x} {xs}) = y'
lem-subset-alt x .(x' ∷ xs) ys xs⊂ys (∈-drop {.x} {x'} {xs} y) = lem-subset-alt x xs ys (lem-⊂-cons-inv-tail x' xs ys xs⊂ys) y

lem-⊂-ext : ∀ {A : Set}(x : A)(xs ys : List A) → xs ⊂ ys → xs ⊂ x ∷ ys
lem-⊂-ext x .[] ys nil = nil
lem-⊂-ext x .(m ∷ ms) ys (cons {m} {ms} y y') = cons (lem-⊂-ext x ms ys y) (∈-drop y')

lem-⊂-cong : ∀ {A : Set}{x : A}{xs ys : List A} → xs ⊂ ys → x ∷ xs ⊂ x ∷ ys
lem-⊂-cong {A} {x} {xs} {ys} sub = cons (lem-⊂-ext x xs ys sub) ∈-take

{- BASE subset lem-⊂-cons-inv-head lem-⊂-cons-inv-tail lem-subset-alt lem-⊂-ext lem-⊂-cong -}

⊂-refl : ∀ {A : Set}(xs : List A) → xs ⊂ xs
⊂-refl [] = nil
⊂-refl (x ∷ xs) = cons (lem-⊂-ext x xs xs (⊂-refl xs)) ∈-take

⊂-trans : ∀ {A : Set}{xs ys zs : List A} → xs ⊂ ys → ys ⊂ zs → xs ⊂ zs
⊂-trans {A} {.[]} {ys} {zs} nil yz = nil
⊂-trans {A} {.(m ∷ ms)} {ys} {zs} (cons {m} {ms} y y') yz = cons (⊂-trans y yz) (lem-subset-alt m ys zs yz y')

{- BASE subset ⊂-refl ⊂-trans -}

-- decidable subset checking

subsetDec : {A : Set} (xs ys : List A) → (eq : Decidable {A = A} _≡_) → Dec (xs ⊂ ys)
subsetDec [] ys eq = yes nil
subsetDec (x ∷ xs) ys eq with subsetDec xs ys eq
subsetDec (x ∷ xs) ys eq | yes p with member x ys eq
subsetDec (x ∷ xs) ys eq | yes p' | yes p = yes (cons p' p)
subsetDec (x ∷ xs) ys eq | yes p  | no ¬p = no (λ x' → ¬p (lem-⊂-cons-inv-head x xs ys x'))
subsetDec (x ∷ xs) ys eq | no ¬p = no (λ x' → ¬p (lem-⊂-cons-inv-tail x xs ys x'))

-----------------------
--  ∈, ⊂ and length  --
-----------------------

lem-positiveLen-nonEmpty : ∀ {A : Set} (l : List A) → 0 < length l → l ≢ []
lem-positiveLen-nonEmpty [] () x'
lem-positiveLen-nonEmpty (x ∷ xs) x' ()

lem-nonEmpty-positiveLen : ∀ {A : Set} (l : List A)  → l ≢ [] → 0 < length l
lem-nonEmpty-positiveLen [] x = ⊥-elim (x refl)
lem-nonEmpty-positiveLen (x ∷ xs) x' = s≤s z≤n

lem-positiveLen-exists : ∀ {A : Set} (l : List A) → 0 < length l → ∃ (λ (x : A) → x ∈ l)
lem-positiveLen-exists [] ()
lem-positiveLen-exists (h ∷ t) p = h , ∈-take

lem-exists-positiveLen : ∀ {A : Set} (l : List A) → ∃ (λ (x : A) → x ∈ l) → 0 < length l
lem-exists-positiveLen [] (h , ())
lem-exists-positiveLen (x ∷ xs) p = s≤s z≤n

lem-subset-not-in : ∀ {A : Set}(y : A)(xs ys : List A) → xs ⊂ (y ∷ ys) → y ∉ xs → xs ⊂ ys
lem-subset-not-in y .[] ys nil nin = nil
lem-subset-not-in y .(y ∷ ms) ys (cons {.y} {ms} y' ∈-take) nin = ⊥-elim (nin ∈-take)
lem-subset-not-in y .(m ∷ ms) ys (cons {m} {ms} y' (∈-drop y0)) nin = cons (lem-subset-not-in y ms ys y' (λ x → nin (∈-drop x))) y0


lem-subset-app : ∀ {A : Set}(xs ys zs : List A) (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → xs ⊂ (ys ++ zs) → 
  ∃₂ (λ (as bs : List A) → length xs ≡ length (as ++ bs) × as ⊂ ys × bs ⊂ zs)
lem-subset-app .[] ys zs cmp nil = [] , [] , refl , nil , nil
lem-subset-app .(m ∷ ms) ys zs cmp (cons {m} {ms} y y') with lem-subset-app ms ys zs cmp y
lem-subset-app .(m ∷ ms) ys zs cmp (cons {m} {ms} y y') | as , bs , lens , asub , bsuc with lem-∈-app m ys zs cmp y'
... | inj₁ m∈ys = m ∷ as , bs , cong suc lens , cons asub m∈ys , bsuc
... | inj₂ m∈zs = as , m ∷ bs , trans (trans (cong suc (trans lens (lem-length-app as bs))) 
          (lem-plus-s (foldr (λ x → suc) zero as) (foldr (λ x → suc) zero bs))) 
          (sym (lem-length-app as (m ∷ bs))) , asub , cons bsuc m∈zs


-- this is not true, this will be true if we suppose the has no repetitions
postulate 
  lem-subset-length : ∀ {A : Set}(xs ys : List A)(cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → distinct xs → xs ⊂ ys → length xs ≤ length ys

{-
lem-subset-length : ∀ {A : Set}(xs ys : List A)(cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → distinct xs → xs ⊂ ys → length xs ≤ length ys
lem-subset-length .[] ys cmp dist nil = z≤n
lem-subset-length .(m ∷ ms) ys cmp (dist-cons dist y) (cons {m} {ms} y' y0) with lem-exists-find m ys y0
lem-subset-length .(m ∷ ms) ys cmp (dist-cons dist y) (cons {m} {ms} y' y0) | as , bs , p rewrite p with lem-subset-app ms as (m ∷ bs) cmp y'
... | l1 , l2 , lens , sub1 , sub2 rewrite lens = {!!}
-}  
{-
    lem-≤-trans (s≤s (lem-≤-eq (sym (lem-length-app l1 l2)) 
   (lem-≤-cong2 (lem-subset-length l1 as cmp {!!} sub1) (lem-subset-length l2 (m ∷ bs) cmp {!!} sub2)))) 
   (lem-≤-trans {!!} (lem-≤-eq-refl (sym (lem-length-app as (m ∷ bs)))))
  -}

  -- zabraklo usuniecia jednego suca, mam to na papierze

{-with lem-subset-length ms (as ++ m ∷ bs) cmp dist y'
... | rec = {!!} -}


{- BASE length lem-positiveLen-exists lem-positiveLen-nonEmpty lem-nonEmpty-positiveLen 
               lem-exists-positiveLen -}

--------------------------------------------------------------------------------
--  Existence of a elem in a list with a certain property relation and query  --
--------------------------------------------------------------------------------

data Any {A : Set} : (P : A → Set) → (l : List A) → Set₁ where
  any-this  : {P : A → Set}{a : A}{l : List A} → P a     → Any P (a ∷ l)
  any-other : {P : A → Set}{a : A}{l : List A} → Any P l → Any P (a ∷ l)
  
lem-any-exists : {A : Set} (P : A → Set) (l : List A) → Any P l → ∃ (λ (a : A) → a ∈ l × P a)
lem-any-exists P .(a ∷ l)      (any-this  {.P} {a} {l} y) = a , ∈-take , y
lem-any-exists P .(a ∷ [])     (any-other {.P} {a} {[]} ())
lem-any-exists P .(a ∷ x ∷ xs) (any-other {.P} {a} {x ∷ xs} y) with lem-any-exists P (x ∷ xs) y
lem-any-exists P .(a ∷ x ∷ xs) (any-other {.P} {a} {x ∷ xs} y) | a0 , inn , Pa0 = a0 , ∈-drop inn , Pa0

lem-any-exists-inv : {A : Set} (P : A → Set) (l : List A) → ∃ (λ (a : A) → a ∈ l × P a) → Any P l
lem-any-exists-inv P .(a0 ∷ xs) (a0 , ∈-take {.a0} {xs} , Pa0)       = any-this Pa0
lem-any-exists-inv P .(x ∷ xs)  (a0 , ∈-drop {.a0} {x} {xs} y , Pa0) = any-other (lem-any-exists-inv P xs (a0 , y , Pa0))

lem-none-exists : {A : Set} (P : A → Set) (l : List A) → ¬ Any P l → ¬ ∃ (λ (a : A) → a ∈ l × P a)
lem-none-exists P l x x' = x (lem-any-exists-inv P l x')

lem-any-nhead-ncons-nlist : {A : Set} (P : A → Set) (a : A)(xs : List A) → (¬ P a) → (¬ Any P xs) → ¬ Any P (a ∷ xs)
lem-any-nhead-ncons-nlist P a xs ¬Pa ¬Pxs (any-this y)  = ¬Pa y
lem-any-nhead-ncons-nlist P a xs ¬Pa ¬Pxs (any-other y) = ¬Pxs y

{- BASE any lem-any-nhead-ncons-nlist lem-any-exists lem-none-exists -}

any-dec : {A : Set} (P : A → Set) (l : List A) → ((a : A) → Dec (P a)) → Dec (Any P l)
any-dec P [] decP = no (λ ())
any-dec P (x ∷ xs) decP with decP x
any-dec P (x ∷ xs) decP | yes p = yes (any-this p)
any-dec P (x ∷ xs) decP | no ¬p with any-dec P xs decP
any-dec P (x ∷ xs) decP | no ¬p  | yes p = yes (any-other p)
any-dec P (x ∷ xs) decP | no ¬p' | no ¬p = no (lem-any-nhead-ncons-nlist P x xs ¬p' ¬p)

------------------------
--  Certified filter  --
------------------------

filterDec : {A : Set} {P : A → Set} → (l : List A) → (decP : ((a : A) → Dec (P a))) → List A
filterDec [] decP = []
filterDec (x ∷ xs) decP with decP x
filterDec (x ∷ xs) decP | yes p = x ∷ filterDec xs decP
filterDec (x ∷ xs) decP | no ¬p = filterDec xs decP


filterDec-valid : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) → P a →
                                          a ∈ l → a ∈ filterDec l decP
filterDec-valid .(a ∷ xs) decP a Pa (∈-take {.a} {xs}) with decP a
filterDec-valid .(a ∷ xs) decP a Pa (∈-take {.a} {xs}) | yes p = ∈-take
filterDec-valid .(a ∷ xs) decP a Pa (∈-take {.a} {xs}) | no ¬p = ⊥-elim (¬p Pa)
filterDec-valid .(x ∷ xs) decP a Pa (∈-drop {.a} {x} {xs} y) with decP x
... | yes p = ∈-drop (filterDec-valid xs decP a Pa y)
... | no ¬p = filterDec-valid xs decP a Pa y


filterDec-valid-rev : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) →
                                               a ∈ filterDec l decP → a ∈ l × P a
filterDec-valid-rev [] decP a ()
filterDec-valid-rev (x ∷ xs) decP a a∈filter with decP x
filterDec-valid-rev (x ∷ xs) decP .x ∈-take | yes p = ∈-take , p
filterDec-valid-rev (x ∷ xs) decP a (∈-drop y) | yes p with filterDec-valid-rev xs decP a y
... | a∈l , Pa = ∈-drop a∈l , Pa
filterDec-valid-rev (x ∷ xs) decP a a∈filter | no ¬p with filterDec-valid-rev xs decP a a∈filter
filterDec-valid-rev (x ∷ xs) decP a a∈filter | no ¬p | a∈l , Pa = ∈-drop a∈l , Pa

filterDec-length : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → length (filterDec l decP) ≤ length l
filterDec-length [] decP = z≤n
filterDec-length (x ∷ xs) decP with decP x
filterDec-length (x ∷ xs) decP | yes p = s≤s (filterDec-length xs decP)
filterDec-length (x ∷ xs) decP | no ¬p = lem-≤-trans (filterDec-length xs decP) (lem-≤-suc (foldr (λ x' → suc) zero xs))

{- BASE filter filterDec-valid-rev filterDec-valid -}

--------------------------------
--  Certified dual to filter  --
--------------------------------

removeDec : {A : Set} {P : A → Set} → (l : List A) → (decP : ((a : A) → Dec (P a))) → List A
removeDec [] decP = []
removeDec (x ∷ xs) decP with decP x
removeDec (x ∷ xs) decP | yes p = removeDec xs decP
removeDec (x ∷ xs) decP | no ¬p = x ∷ removeDec xs decP

removeDec-valid : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) → ¬ P a →
                                          a ∈ l → a ∈ removeDec l decP
removeDec-valid .(a ∷ xs) decP a ¬Pa (∈-take {.a} {xs}) with decP a
... | yes p = ⊥-elim (¬Pa p)
... | no ¬p = ∈-take
removeDec-valid .(x ∷ xs) decP a ¬Pa (∈-drop {.a} {x} {xs} y) with decP x
... | yes p = removeDec-valid xs decP a ¬Pa y
... | no ¬p = ∈-drop (removeDec-valid xs decP a ¬Pa y)

removeDec-valid-rev : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) →
                                               a ∈ removeDec l decP → a ∈ l × ¬ P a
removeDec-valid-rev [] decP a ()
removeDec-valid-rev (x ∷ xs) decP a a∈remove with decP x
... | yes p with removeDec-valid-rev xs decP a a∈remove
removeDec-valid-rev (x ∷ xs) decP a a∈remove | yes p | a∈l , ¬Pa = ∈-drop a∈l , ¬Pa
removeDec-valid-rev (x ∷ xs) decP .x ∈-take  | no ¬p = ∈-take , ¬p
removeDec-valid-rev (x ∷ xs) decP a (∈-drop y) | no ¬p with removeDec-valid-rev xs decP a y
... | a∈l , ¬Pa = ∈-drop a∈l , ¬Pa

-- QUESTION:
-- can't this be done ony by using removeDec-valid? (just like removeDec-valid2-rev only use removeDec-valid-rev)

removeDec-valid2 : {A : Set} {P : A → Set} (l : List A) (_==_ : Decidable{A = A} _≡_)(decP : ((a : A) → Dec (P a))) → (a : A) → 
                                      a ∈ l → a ∉ removeDec l decP → P a
removeDec-valid2 .(a ∷ xs) eq decP a (∈-take {.a} {xs}) a∉remove with decP a
... | yes p = p
... | no ¬p = ⊥-elim (a∉remove ∈-take)
removeDec-valid2 .(x ∷ xs) eq decP a (∈-drop {.a} {x} {xs} y) a∉remove with decP x
... | yes p = removeDec-valid2 xs eq decP a y a∉remove
removeDec-valid2 .(x ∷ xs) eq decP a (∈-drop {.a} {x} {xs} y) a∉remove | no ¬p with eq a x
... | yes p' rewrite p' = ⊥-elim (a∉remove ∈-take)
... | no ¬p' = removeDec-valid2 xs eq decP a y (λ x' → a∉remove (∈-drop x'))

removeDec-valid2-rev : {A : Set} {P : A → Set} (l : List A)(decP : ((a : A) → Dec (P a))) 
                       → (a : A) → a ∈ l → P a → a ∉ removeDec l decP
removeDec-valid2-rev l decP a a∈l Pa a∈remove = (proj₂ (removeDec-valid-rev l decP a a∈remove)) Pa

removeDec-nin : {A : Set} {P : A → Set} (l : List A)(decP : ((a : A) → Dec (P a))) → (a : A) → a ∉ l 
    → a ∉ removeDec l decP
removeDec-nin l decP a a∉l a∈remove = a∉l (proj₁ (removeDec-valid-rev l decP a a∈remove))

removeDec-subset : {A : Set} {P : A → Set} (l : List A)(decP : ((a : A) → Dec (P a))) → removeDec l decP ⊂ l
removeDec-subset [] decP = nil
removeDec-subset (x ∷ xs) decP with decP x
removeDec-subset (x ∷ xs) decP | yes p = lem-⊂-ext x (removeDec xs decP) xs (removeDec-subset xs decP)
removeDec-subset (x ∷ xs) decP | no ¬p = cons (lem-⊂-ext x ((removeDec xs decP)) xs (removeDec-subset xs decP)) ∈-take

removeDec-distinct : {A : Set} {P : A → Set} (l : List A)(decP : ((a : A) → Dec (P a))) 
                     → distinct l → distinct (removeDec l decP)
removeDec-distinct [] decP dist = dist
removeDec-distinct (x ∷ xs) decP dist with decP x
removeDec-distinct (x ∷ xs) decP (dist-cons dist y) | yes p = removeDec-distinct xs decP dist
removeDec-distinct {A} {P} (x ∷ xs) decP (dist-cons dist y) | no ¬p = dist-cons (removeDec-distinct xs decP dist) 
                                                                                (removeDec-nin xs decP x y)

removeDec-pred-subset : {A : Set} {P1 P2 : A → Set} (l : List A)(decP1 : ((a : A) → Dec (P1 a)))(decP2 : ((a : A) → Dec (P2 a)))
                       → ((a : A) → P2 a → P1 a) → removeDec l decP1 ⊂ removeDec l decP2
removeDec-pred-subset [] decP1 decP2 impl = nil
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl with decP2 x 
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl | yes p with decP1 x | impl x p
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl | yes p | yes p' | p2 = removeDec-pred-subset xs decP1 decP2 impl
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl | yes p | no ¬p | p2 = ⊥-elim (¬p p2)
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl | no ¬p with decP1 x
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl | no ¬p | yes p 
   = lem-⊂-ext x (removeDec xs decP1) ((removeDec xs decP2)) (removeDec-pred-subset xs decP1 decP2 impl)
removeDec-pred-subset (x ∷ xs) decP1 decP2 impl | no ¬p' | no ¬p = lem-⊂-cong (removeDec-pred-subset xs decP1 decP2 impl)

{- BASE remove removeDec-valid-rev removeDec-valid removeDec-valid2 removeDec-subset -}

removeDec-length : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → length (removeDec l decP) ≡ length l ∸ length (filterDec l decP)
removeDec-length [] decP = refl
removeDec-length (x ∷ xs) decP with decP x
removeDec-length (x ∷ xs) decP | yes p = removeDec-length xs decP
removeDec-length (x ∷ xs) decP | no ¬p rewrite removeDec-length xs decP = lem-minus-eq (length xs) (length (filterDec xs decP)) (filterDec-length xs decP)

{-
----------------------------------------
      Properties of permutations
----------------------------------------
-}

data Permutation {A : Set} : (l1 l2 : List A) → Set where
  p-nil   : Permutation [] []
  p-cons  : (x : A) (xs xs' : List A) → Permutation xs xs' → Permutation (x ∷ xs) (x ∷ xs')
  p-swap  : (x y : A)(l : List A) → Permutation (x ∷ y ∷ l) (y ∷ x ∷ l)
  p-trans : (l1 l2 l3 : List A) → Permutation l1 l2 → Permutation l2 l3 → Permutation l1 l3


perm-id : ∀ {A : Set}(l : List A) → Permutation l l
perm-id [] = p-nil
perm-id (x ∷ xs) = p-cons x xs xs (perm-id xs)

perm-sym : ∀ {A : Set}(l1 l2 : List A) → Permutation l1 l2 → Permutation l2 l1
perm-sym .[] .[] p-nil = p-nil
perm-sym .(x ∷ xs) .(x ∷ xs') (p-cons x xs xs' y) = p-cons x xs' xs (perm-sym xs xs' y)
perm-sym .(x ∷ y ∷ l) .(y ∷ x ∷ l) (p-swap x y l) = p-swap y x l
perm-sym l1 l2 (p-trans .l1 l3 .l2 y y') = p-trans l2 l3 l1 (perm-sym l3 l2 y') (perm-sym l1 l3 y)

{- BASE perm perm-id perm-sym -}

perm-in : ∀ {A : Set}(x : A)(l l' : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → 
          Permutation l l' →  x ∈ l → x ∈ l'
perm-in x .[] .[] cmp p-nil x∈l = x∈l
perm-in .x' .(x' ∷ xs) .(x' ∷ xs') cmp (p-cons x' xs xs' y) (∈-take {.x'} {.xs}) = ∈-take
perm-in x .(x' ∷ xs) .(x' ∷ xs') cmp (p-cons x' xs xs' y) (∈-drop y') = ∈-drop (perm-in x xs xs' cmp y y')
perm-in .x' .(x' ∷ y ∷ l) .(y ∷ x' ∷ l) cmp (p-swap x' y l) (∈-take {.x'} {.(y ∷ l)}) = ∈-drop ∈-take
perm-in .y .(x' ∷ y ∷ l) .(y ∷ x' ∷ l) cmp (p-swap x' y l) (∈-drop (∈-take {.y} {.l})) = ∈-take
perm-in x .(x' ∷ y ∷ l) .(y ∷ x' ∷ l) cmp (p-swap x' y l) (∈-drop (∈-drop y')) = ∈-drop (∈-drop y')
perm-in x l l' cmp (p-trans .l l2 .l' y y') x∈l = perm-in x l2 l' cmp y' (perm-in x l l2 cmp y x∈l)


perm-in-rev : ∀ {A : Set}(x : A)(l l' : List A) → (cmp : ∀ (a1 a2 : A) → Dec (a1 ≡ a2)) → 
               Permutation l l' →  x ∈ l' → x ∈ l
perm-in-rev x .[] .[] x' p-nil x1 = x1
perm-in-rev .x0 .(x0 ∷ xs) .(x0 ∷ xs') x' (p-cons x0 xs xs' y) (∈-take) = ∈-take
perm-in-rev x .(x0 ∷ xs) .(x0 ∷ xs') x' (p-cons x0 xs xs' y) (∈-drop y') = ∈-drop (perm-in-rev x xs xs' x' y y')
perm-in-rev .y .(x0 ∷ y ∷ l) .(y ∷ x0 ∷ l) x' (p-swap x0 y l) (∈-take) = ∈-drop ∈-take
perm-in-rev .x0 .(x0 ∷ y ∷ l) .(y ∷ x0 ∷ l) x' (p-swap x0 y l) (∈-drop (∈-take)) = ∈-take
perm-in-rev x .(x0 ∷ y ∷ l) .(y ∷ x0 ∷ l) x' (p-swap x0 y l) (∈-drop  (∈-drop y')) = ∈-drop (∈-drop y')
perm-in-rev x l l' x' (p-trans .l l2 .l' y y') x1 = perm-in-rev x l l2 x' y (perm-in-rev x l2 l' x' y' x1)

{- BASE in perm-in perm-in-rev -}
{- BASE perm perm-in perm-in-rev -}


perm-swap : ∀ {A : Set}(x y : A)(l1 l2 : List A) → Permutation l1 l2 → Permutation (x ∷ y ∷ l1) (y ∷ x ∷ l2)
perm-swap x y .[] .[] p-nil = p-swap x y []
perm-swap x y .(x' ∷ xs) .(x' ∷ xs') (p-cons x' xs xs' y') = p-trans (x ∷ y ∷ x' ∷ xs) (y ∷ x ∷ x' ∷ xs) (y ∷ x ∷ x' ∷ xs')
                                                               (p-swap x y (x' ∷ xs))
                                                               (p-cons y (x ∷ x' ∷ xs) (x ∷ x' ∷ xs')
                                                                (p-cons x (x' ∷ xs) (x' ∷ xs') (p-cons x' xs xs' y')))
perm-swap x y .(x' ∷ y' ∷ l) .(y' ∷ x' ∷ l) (p-swap x' y' l) = p-trans (x ∷ y ∷ x' ∷ y' ∷ l) (y ∷ x ∷ x' ∷ y' ∷ l)
                                                                 (y ∷ x ∷ y' ∷ x' ∷ l) (p-swap x y (x' ∷ y' ∷ l))
                                                                 (p-cons y (x ∷ x' ∷ y' ∷ l) (x ∷ y' ∷ x' ∷ l)
                                                                  (p-cons x (x' ∷ y' ∷ l) (y' ∷ x' ∷ l) (p-swap x' y' l)))
perm-swap x y l1 l2 (p-trans .l1 l3 .l2 y' y0) = p-trans (x ∷ y ∷ l1) (y ∷ x ∷ l3) (y ∷ x ∷ l2)
                                                   (perm-swap x y l1 l3 y')
                                                   (p-cons y (x ∷ l3) (x ∷ l2) (p-cons x l3 l2 y0)) 


perm-nil : ∀ {A : Set}(l : List A) → Permutation [] l → l ≡ []
perm-nil [] perm = refl
perm-nil (x ∷ xs) (p-trans .[] l2 .(x ∷ xs) y y') rewrite (perm-nil l2 y) = perm-nil (x ∷ xs) y' 

{- BASE perm perm-swap perm-nil -}

postulate
  perm-app : ∀ {A : Set}(xs xs' ys ys' : List A) → Permutation xs xs' → Permutation ys ys' → Permutation (xs ++ ys) (xs' ++ ys')

{- BASE perm perm-app -}


{- the following proof typechecks, but may not be terminating -}

{-
perm-app : ∀ {A : Set}(xs xs' ys ys' : List A) → Permutation xs xs' → Permutation ys ys' → Permutation (xs ++ ys) (xs' ++ ys')
perm-app .[] .[] ys ys' p-nil perm-ys' = perm-ys'
perm-app .(x ∷ xs) .(x ∷ xs') ys ys' (p-cons x xs xs' y) perm-ys' = p-cons x (xs ++ ys) (xs' ++ ys')
                                                                      (perm-app xs xs' ys ys' y perm-ys')
perm-app .(x ∷ y ∷ l) .(y ∷ x ∷ l) ys ys' (p-swap x y l) perm-ys' = perm-swap x y (l ++ ys) (l ++ ys') (perm-app l l ys ys' (perm-id l) perm-ys')
perm-app xs xs' ys ys' (p-trans .xs l2 .xs' y y') perm-ys' = p-trans ((xs ++ ys)) ((l2 ++ ys')) ((xs' ++ ys')) p1 p2 where
  p1 : Permutation (xs ++ ys) (l2 ++ ys')
  p1 = perm-app xs l2 ys ys' y perm-ys'  

  p2 : Permutation (l2 ++ ys') (xs' ++ ys')
  p2 = perm-app l2 xs' ys' ys' y' (perm-id ys')
-}

-----------------------------------------------------------------------------------------------
--  A version of map for situation whens a proof of membership is required for calculations  --
-----------------------------------------------------------------------------------------------

map-in : {A B : Set} → (l : List A) → (f : (a : A) → a ∈ l → B) → List B
map-in [] _ = []
map-in {A} {B} (x ∷ xs) f = f x ∈-take ∷ map-in xs f' where
  f' : (a : A) → a ∈ xs → B
  f' a a∈xs = f a (∈-drop a∈xs)

lem-length-map-in :  {A B : Set} → (l : List A) → (f : (a : A) → a ∈ l → B) → length (map-in l f) ≡ length l
lem-length-map-in []       f = refl
lem-length-map-in (x ∷ xs) f = cong suc (lem-length-map-in xs (λ a x' → f a (∈-drop x')))

lem-map-in-inv : {A B : Set} → {a0 : B} → (l : List A) → (f : (a : A) → a ∈ l → B) → a0 ∈ map-in l f →
  ∃₂ (λ (a : A) (p : a ∈ l) → a0 ≡ f a p)
lem-map-in-inv [] f () 
lem-map-in-inv (x ∷ xs) f ∈-take = x , ∈-take , refl
lem-map-in-inv {A} {B} {a0} (x ∷ xs) f (∈-drop y) with lem-map-in-inv xs f' y where
  f' : (a : A) (a∈xs : a ∈ xs) → B
  f' a a∈xs = f a (∈-drop a∈xs)
lem-map-in-inv {A} {B} {a0} (x ∷ xs) f (∈-drop y) | a , a∈xs , a0≡a = a , ∈-drop a∈xs , a0≡a

-------------------------
--  Proof irrelevance  --
-------------------------

-- x ∈ xs proof irrelevance 

lem-∈-irrelv : ∀ {A : Set}{a : A}{l} → distinct l → (p1 : a ∈ l) → (p2 : a ∈ l) → p1 ≡ p2
lem-∈-irrelv dist-nil () a∈[]
lem-∈-irrelv (dist-cons dist y) ∈-take ∈-take = refl
lem-∈-irrelv (dist-cons dist y) ∈-take (∈-drop y') = ⊥-elim (y y')
lem-∈-irrelv (dist-cons dist y) (∈-drop y') ∈-take = ⊥-elim (y y')
lem-∈-irrelv (dist-cons dist y) (∈-drop y') (∈-drop y0) = cong ∈-drop (lem-∈-irrelv dist y' y0)
