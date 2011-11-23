module EquationsTemplate where

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

vec-map-lemma f g xs = {!!}
