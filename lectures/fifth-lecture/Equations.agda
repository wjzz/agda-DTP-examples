module Equations where

open import Data.Nat
open import Data.Vec hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

map : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs


vec-map-lemma : {A B C : Set}
              → {n : ℕ} 
              → (f : A → B) 
              → (g : B → C) 
              → (v : Vec A n) 
              → map g (map f v) ≡ map (g ∘ f) v

vec-map-lemma f g []       = refl
vec-map-lemma f g (x ∷ xs) = 
  begin
    map g (map f (x ∷ xs))     ≡⟨ refl ⟩
    g (f x) ∷ map g (map f xs) ≡⟨ cong (_∷_ (g (f x))) (vec-map-lemma f g xs) ⟩
    g (f x) ∷ map (g ∘ f) xs   ≡⟨ refl ⟩
    map (g ∘ f) (x ∷ xs)
  ∎

--vec-map-lemma f g (x ∷ xs) = cong (λ X → (g (f x)) ∷ X) (vec-map-lemma f g xs)

--vec-map-lemma f g (x ∷ xs) rewrite vec-map-lemma f g xs = refl

-- vec-map-lemma f g (x ∷ xs) with vec-map-lemma f g xs
-- ... | rec = cong (λ X → (g (f x)) ∷ X) rec

{-
vec-map-lemma f g (x ∷ xs) = 
  begin
    map g (map f (x ∷ xs))     ≡⟨ refl ⟩
    g (f x) ∷ map g (map f xs) ≡⟨ cong (_∷_ (g (f x))) (vec-map-lemma f g xs) ⟩
    g (f x) ∷ map (g ∘ f) xs   ≡⟨ refl ⟩
    map (g ∘ f) (x ∷ xs)
  ∎
-}