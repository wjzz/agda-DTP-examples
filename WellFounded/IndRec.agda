module IndRec (Var : Set) where
  open import Data.Nat
  open import Data.Bool
  open import Data.Empty
  open import Data.Product
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality

  Store : Set
  Store = Var → ℕ

  module WhileSemBad1
    (
      AExpr  : Set
    ; BExpr  : Set
    ; A⟦_⟧   : AExpr → Store → ℕ
    ; B⟦_⟧   : BExpr → Store → Bool
    ; _[_/_] : Store → Var → ℕ → Store
    ) where

    data CExpr : Set where
      skip   : CExpr
      assign : Var → AExpr → CExpr
      seq    : CExpr → CExpr → CExpr
      while  : BExpr → CExpr → CExpr

    C⟦_⟧ : CExpr → Store → Store

    C⟦_⟧ skip σ         = σ

    C⟦_⟧ (assign v a) σ = σ [ v / A⟦ a ⟧ σ ]

    C⟦_⟧ (seq c₁ c₂) σ  = C⟦ c₂ ⟧ (C⟦ c₁ ⟧ σ)

    C⟦_⟧ (while b c) σ with B⟦ b ⟧ σ 
    ... | false         = σ
    ... | true          = C⟦ while b c ⟧ (C⟦ c ⟧ σ)

  module WhileSemBad2
    (
      AExpr  : Set
    ; BExpr  : Set
    ; A⟦_⟧   : AExpr → Store → ℕ
    ; B⟦_⟧   : BExpr → Store → Bool
    ; _[_/_] : Store → Var → ℕ → Store
    ) where

    data CExpr : Set where
      skip   : CExpr
      assign : Var → AExpr → CExpr
      seq    : CExpr → CExpr → CExpr
      while  : BExpr → CExpr → CExpr


    data Acc : CExpr → Store → Set where
      accSkip   : {σ : Store}
                → Acc skip σ

      accAssign : {v : Var} {a : AExpr} {σ : Store}
                → Acc (assign v a) σ

      accSeq    : {c₁ c₂ : CExpr} {σ : Store}
                → Acc c₁ σ
                → Acc (seq c₁ c₂) σ


  module WhileSemGood
    (
      AExpr  : Set
    ; BExpr  : Set
    ; A⟦_⟧   : AExpr → Store → ℕ
    ; B⟦_⟧   : BExpr → Store → Bool
    ; _[_/_] : Store → Var → ℕ → Store
    ) where

    data CExpr : Set where
      skip   : CExpr
      assign : Var → AExpr → CExpr
      seq    : CExpr → CExpr → CExpr
      while  : BExpr → CExpr → CExpr

    mutual
      data Acc : CExpr → Store → Set where
        accSkip   : {σ : Store}
                  → Acc skip σ
  
        accAssign : {v : Var} {a : AExpr} {σ : Store}
                  → Acc (assign v a) σ
  
        accSeq    : {c₁ c₂ : CExpr} {σ : Store}
                  → (Hc₁ : Acc c₁ σ)
                  → Acc c₂ (C⟦ c₁ ⟧ σ < Hc₁ >)
                  → Acc (seq c₁ c₂) σ

        accWhile0 : {b : BExpr} {c : CExpr} {σ : Store}
                  → B⟦ b ⟧ σ ≡ false
                  → Acc (while b c) σ

        accWhileS : {b : BExpr} {c : CExpr} {σ : Store}
                  → B⟦ b ⟧ σ ≡ true
                  → (Hc : Acc c σ)
                  → Acc (while b c) (C⟦ c ⟧ σ < Hc >)
                  → Acc (while b c) σ


      C⟦_⟧_<_>  : (c : CExpr) → (σ : Store) → Acc c σ → Store
      C⟦ .skip ⟧ σ < accSkip >                            = σ
      C⟦ .(assign v a) ⟧ σ < accAssign {v} {a} >          = σ [ v / A⟦ a ⟧ σ ]
      C⟦ .(seq c₁ c₂) ⟧ σ < accSeq {c₁} {c₂} Hc₁ Hc₂ >    = C⟦ c₂ ⟧ (C⟦ c₁ ⟧ σ < Hc₁ >) < Hc₂ >
      C⟦ .(while b c) ⟧ σ < accWhile0 {b} {c} _ >         = σ
      C⟦ .(while b c) ⟧ σ < accWhileS {b} {c} _ Hc Hw >   = C⟦ while b c ⟧ (C⟦ c ⟧ σ < Hc >) < Hw >


    module Example where

      noLoops : CExpr → Set
      noLoops skip         = ⊤
      noLoops (assign _ _) = ⊤
      noLoops (seq c₁ c₂)  = noLoops c₁ × noLoops c₂
      noLoops (while b c)  = ⊥

      noLoopsAcc : {c : CExpr} → noLoops c → (σ : Store) → Acc c σ
      noLoopsAcc {skip} Hl σ        = accSkip
      noLoopsAcc {assign v a} Hl σ  = accAssign

      noLoopsAcc {seq c₁ c₂}  Hl σ with noLoopsAcc {c₁} (proj₁ Hl) σ
      ... | Hc₁ = accSeq Hc₁ (noLoopsAcc {c₂} (proj₂ Hl) (C⟦ c₁ ⟧ σ < Hc₁ >))

      noLoopsAcc {while b c} Hl σ   = ⊥-elim Hl

      C'⟦_⟧ : (c : CExpr) → (H : noLoops c) → Store → Store
      C'⟦_⟧ c H σ = C⟦ c ⟧ σ < noLoopsAcc H σ >

      --
      data CExpr0 : Set where
        skip0   : CExpr0
        assign0 : Var → AExpr → CExpr0
        seq0    : CExpr0 → CExpr0 → CExpr0

      mapCmd : CExpr0 → CExpr
      mapCmd skip0         = skip
      mapCmd (assign0 v a) = assign v a
      mapCmd (seq0 c₁ c₂)  = seq (mapCmd c₁) (mapCmd c₂)

      mapCmdNoLoops : (c : CExpr0) → noLoops (mapCmd c)
      mapCmdNoLoops skip0           = tt
      mapCmdNoLoops (assign0 c₁ c₂) = tt
      mapCmdNoLoops (seq0 c₁ c₂)    = mapCmdNoLoops c₁ , mapCmdNoLoops c₂

      C0⟦_⟧ : CExpr0 → Store → Store
      C0⟦ c ⟧ = C'⟦ mapCmd c ⟧ (mapCmdNoLoops c)

      --
