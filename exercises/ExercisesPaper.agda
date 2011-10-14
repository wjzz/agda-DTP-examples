module ExercisesPaper where

  module MartinLof where
    -- standard Martin-Lof type theory from Book

    data ℕ∅ : Set where

    case₀ : {C : Set}
          → ℕ∅
          → C
    case₀ ()

    ⊥ : Set
    ⊥ = ℕ∅

    ----

    data ℕ₁ : Set where
      0₁ : ℕ₁

    case₁ : {C : ℕ₁ → Set} 
          → C 0₁
          → (p : ℕ₁) → C p
    case₁ H0 0₁ = H0

    ⊤ : Set
    ⊤ = ℕ₁

    ----

    data ℕ₂ : Set where
      0₂ : ℕ₂
      1₂ : ℕ₂

    case₂ : {C : ℕ₂ → Set}
          → C 0₂ → C 1₂
          → (p : ℕ₂) → C p
    case₂ H0 H1 0₂ = H0
    case₂ H0 H1 1₂ = H1

    Bool : Set
    Bool = ℕ₂

    true  : Bool
    true  = 0₂
    false : Bool
    false = 1₂

    ----

    data ℕ : Set where
      O    : ℕ
      succ : ℕ → ℕ


    natrec : {C : ℕ → Set}
           → C O
           → ( (n : ℕ) → C n → C (succ n) )
           → (n : ℕ) → C n
    natrec H0 HS O        = H0
    natrec H0 HS (succ n) = HS n (natrec H0 HS n)

    ----

    data _⊎_ (A B : Set) : Set where
      inl : A → A ⊎ B
      inr : B → A ⊎ B

    when : {A B : Set} → {C : A ⊎ B → Set}
         → ( (x : A) → C (inl x) )
         → ( (x : B) → C (inr x) )
         → (e : A ⊎ B) → C e
    when HA HB (inl x) = HA x
    when HA HB (inr x) = HB x

    _∨_ : Set → Set → Set
    A ∨ B = A ⊎ B

    ----

    data Π (A : Set) (B : A → Set) : Set where
      Λ : ( (x : A) → B x ) → Π A B

    apply : { A : Set} → { B : A → Set }
          → Π A B → (x : A)
          → B x
    apply (Λ f) x = f x

    syntax Π A (λ x → B) = Π[ x ∶ A ] B
    syntax Λ (λ x → e)   = Λ[ x ] e

    _⇒_ : Set → Set → Set
    A ⇒ B = Π A (λ x → B)

    idf : {A : Set}
        → A ⇒ A
    idf = Λ[ x ] x

    ----

    data Σ (A : Set) (B : A → Set) : Set where
      _,_ : (a : A) → B a → Σ A B

    split : {A : Set} {B : A → Set} {C : Σ A B → Set}
          → ( (a : A) → (b : B a) → C (a , b) )
          → (p : Σ A B) → C p
    split H (a , b) = H a b

    syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

    _×_ : Set → Set → Set
    A × B = Σ A (λ x → B)

    ----

    data W (A : Set) (B : A → Set) : Set where
      sup : (a : A) → (f : B a → W A B) → W A B

    W-elim : {A : Set} {B : A → Set} {C : W A B → Set}
           → ( (a : A) → (f : B a → W A B) → ((b : B a) → C (f b)) → C (sup a f))
           → (p : W A B) → C p

    W-elim {A} {B} {P} H (sup a f) = H a f (λ b → W-elim {A} {B} {P} H (f b))

    ----

    data _≡_ {A : Set} : A → A → Set where
      id : (x : A) →  x ≡ x

    idpeel : {A : Set} → {a b : A} → {C : (a b : A) → a ≡ b → Set}
           → ( (x : A) → C x x (id x) )
           → (z : a ≡ b) → C a b z

    idpeel H (id x) = H x

    ---

    ¬_ : (C : Set) → Set
    ¬ C = C ⇒ ⊥


  module Task1 where
    open MartinLof

    data List (A : Set) : Set where
      nil  : List A
      cons : A → List A → List A

    listrec : {A : Set} → {C : List A → Set}
            → C nil
            → ( (x : A) → (xs : List A) → C xs → C (cons x xs) )
            → (xs : List A) → C xs
    listrec Hnil Hcons nil = Hnil
    listrec Hnil Hcons (cons x xs) = Hcons x xs (listrec Hnil Hcons xs)

    data Tree (A : Set) : Set where
      leaf : Tree A
      node : A → Tree A → Tree A → Tree A

    treerec : {A : Set} → {C : Tree A → Set}
            → C leaf
            → ( (x : A) → (l r : Tree A) → C l → C r → C (node x l r) )
            → (xs : Tree A) → C xs
    treerec Hl Hn leaf = Hl
    treerec Hl Hn (node x l r) = Hn x l r (treerec Hl Hn l) (treerec Hl Hn r)

  module MartinLofWithUniverse where
    open MartinLof public
    open Task1 public

    ---

    mutual
      data U : Set where
        n₀   : U
        n₁   : U
        n₂   : U
        ⊕    : U → U → U
        σ    : (a : U) → (T a → U) → U
        π    : (a : U) → (T a → U) → U
        N    : U
        w    : (a : U) → (T a → U) → U
        i    : (a : U) → T a → T a → U
        list : U → U
        tree : U → U

      T : U -> Set
      T n₀        = ℕ∅
      T n₁        = ℕ₁
      T n₂        = ℕ₁
      T N         = ℕ
      T (⊕ a b)   = T a ⊎ T b
      T (σ a b)   = Σ[ x ∶ T a ] T (b x)
      T (π a b)   = Π[ x ∶ T a ] T (b x)
      T (w a b)   = W (T a) (\x -> T (b x))
      T (i a b c) = b ≡ c
      T (list a)  = List (T a)
      T (tree a)  = Tree (T a)


  module Task2 where
    open MartinLof

    -- done as ⊎


  module Task3 (A : Set ; B : A → Set ; C : A → A → Set) where
    open MartinLof

    thm1 : (Π[ x ∶ A ] Π[ y ∶ A ] C x y) ⇒ (Π[ y ∶ A ] Π[ x ∶ A ] C x y)
    thm1 = Λ[ H ] Λ[ y ] Λ[ x ] apply (apply H x) y

    thm2 : (Σ[ x ∶ A ] Π[ y ∶ A ] C x y) ⇒ (Π[ y ∶ A ] Σ[ x ∶ A ] C x y)
    thm2 = Λ[ H ] Λ[ y ] split (λ a b → a , apply b y) H

    thm3 : (Π[ x ∶ A ] Π[ y ∶ A ] ( B x ⇒ B y ) )
         ⇒ (Π[ x ∶ A ] Π[ y ∶ A ] ( ¬ B y ⇒ ¬ B x ) )
    thm3 = Λ[ H ] Λ[ x ] Λ[ y ] Λ[ HNBy ] Λ[ HBx ]
           apply HNBy (apply (apply (apply H x) y) HBx)

    thm4 : ¬ (Σ[ x ∶ A ] B x)
         ⇒ (Π[ x ∶ A ] ¬ B x)
    thm4 = Λ[ H ] Λ[ x ] Λ[ HBx ] apply H (x , HBx)

  module Task4 (A : Set; B' : Set; C' : Set; B : A → Set; C : (x : A) → B x → Set) where
    open MartinLof

    compose : (f : B' ⇒ C') → (g : A ⇒ B') → A ⇒ C'
    compose f g = Λ[ x ] apply f (apply g x)

    composeDep : (f : Π[ x ∶ A ] (Π[ b ∶ B x ] C x b)) → (g : Π A B)
               → Π[ x ∶  A ] C x (apply g x)

    composeDep f g = Λ[ x ] apply (apply f x) (apply g x)

    apply2 : (Π[ x ∶ A ] Π[ b ∶ B x ] C x b)
           → (x : A) → (y : B x)
           → C x y
    apply2 f x y = apply (apply f x) y


  module Task5 (A : Set) where
    open MartinLof

    thm1 : Π[ x ∶ A ] x ≡ x
    thm1 = Λ[ x ] (id x)

    thm2 : Π[ b ∶ Bool ] Π[ c ∶ A ] case₂ c c b ≡ c
    thm2 = Λ[ b ] Λ[ c ] (case₂ {C = λ b → case₂ c c b ≡ c} (id c) (id c) b)



  module Task6 where
    open MartinLof

    subst : {A : Set} {a b : A} → {P : A → Set}
          → (a ≡ b)
          → P a
          → P b

    subst {P = P} c p
      = apply (idpeel {C = λ a b z → P a ⇒ P b} (λ x → Λ[ y ] y ) c) p

    symm : {A : Set} {a b : A}
         → (a ≡ b)
         → (b ≡ a)
    symm {A} {a} {b} c = subst {P = λ x → x ≡ a} c (id a)


    trans : {A : Set} {a b c : A}
         → (a ≡ b)
         → (b ≡ c)
         → (a ≡ c)

    trans {A} {a} {b} {c} p1 p2 
      = apply (subst {P = λ x → (b ≡ c) ⇒ (x ≡ c)} (symm p1) (Λ[ y ] y)) p2

    cong : {A : Set} {B : Set} {a b : A}
         → (a ≡ b)
         → (f : A ⇒ B)
         → (apply f a ≡ apply f b)
    cong {A} {B} {a} {b} c f
      = subst {P = λ x → apply f a ≡ apply f x} c (id (apply f a))


  module Task9 where
    open MartinLof
    open Task6

    thm : {A B : Set}
        → (f g : A ⇒ B)
        → f ≡ g
        → Π[ x ∶ A ] apply f x ≡ apply g x
    thm f g H = Λ[ x ] subst
        {P = λ p → apply f x ≡ apply p x}
        H (id (apply f x))

  module Task10 where
    open MartinLofWithUniverse
    open Task6

    H01 : Π[ n ∶ ℕ ] ¬ (O ≡ succ n)
    H01 = Λ[ n ] Λ[ Heq ] subst {P = λ x → IsZero x} (Heq) 0₁
     where
       IsZero : ℕ → Set
       IsZero n = T (natrec n₁ (λ _ _ → n₀) n)

  module Task11 where
    open MartinLofWithUniverse
    open Task6

    Empty : {A : Set}
          → List A
          → Set
    Empty xs = T (listrec n₁ (λ _ _ _ → n₀) xs)

    isEmpty : {A : Set}
            → Π[ xs ∶ List A ] Empty xs ∨ ¬ Empty xs
    isEmpty = Λ[ xs ] listrec
                 {C = λ xs → Empty xs ∨ ¬ Empty xs}
                 (inl 0₁)
                 (λ x xs _ → inr (Λ (λ H' → H')))
                 xs

    head : {A : Set}
         → Π[ xs ∶ List A ] (¬ (Empty xs) ⇒ A)
    head {A} = Λ[ xs ] listrec {C = λ xs →  ¬ (Empty xs) ⇒ A}
           (Λ[ H ] case₀ (apply H 0₁))
           (λ x _ _ → Λ (λ H → x))
           xs

    tail : {A : Set}
         → Π[ xs ∶ List A ] (¬ (Empty xs) ⇒ List A)
    tail {A} = Λ[ xs ] listrec {C = λ xs →  ¬ (Empty xs) ⇒ List A}
           (Λ[ H ] case₀ (apply H 0₁))
           (λ _ xs _ → Λ (λ H → xs))
           xs


  module Task12 where
    open MartinLofWithUniverse
    open Task6

    negb : Bool ⇒ Bool
    negb = Λ[ b ] case₂ false true b

    H01 : ¬ (0₂ ≡ 1₂)
    H01 = Λ[ Heq ] subst {P = λ x → IsZero x} Heq 0₁
     where
       IsZero : Bool → Set
       IsZero b = T (case₂ n₁ n₀ b)

    Hnegb : Π[ b ∶ Bool ] ¬ (b ≡ apply negb b)
    Hnegb = Λ[ b ] case₂ {C = λ b → ¬ (b ≡ apply negb b)}
      (H01)
      (Λ[ H ] apply H01 (symm H))
      b 


  module Task13 where
    open MartinLofWithUniverse
    open Task6
    open Task12

    BinSeq : Set
    BinSeq = ℕ ⇒ Bool

    cantor : ¬ (Σ[ f ∶ ℕ ⇒ BinSeq ] (Σ[ g ∶ BinSeq ⇒ ℕ ]
             Π[ s ∶ BinSeq ] s ≡ (apply f (apply g s))))
           
    cantor = Λ (λ H → split (λ f → split (λ g H0 → diagonal f g H0) ) H)
      where
       diagonal : (f : ℕ ⇒ BinSeq) → (g : BinSeq ⇒ ℕ)
                → Π[ s ∶ BinSeq ] s ≡  (apply f (apply g s))
                → ⊥
       diagonal f g Heq = apply (apply Hnegb (apply s h)) thm2
         where
           -- diagonal sequence: s(n) = neg (f n n)
           s : BinSeq
           s = Λ[ n ] apply negb (apply (apply f n) n)

           -- number of s
           h : ℕ
           h = apply g s

           -- paradox: s h = negb (f h h) = negb (f (g s) h) = negb (s h)
           -- first two equations are definitional, so we need to prove only
           -- last
           thm2 :
                apply s h
                ≡
                apply negb (apply s h)

           thm2 = subst
                  {P = λ x → apply negb (apply x h) ≡ apply negb (apply s h)}
                  (apply Heq s) (id (apply negb (apply s h)))

