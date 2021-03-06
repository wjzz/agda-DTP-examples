-- Rozwiazania do pierwszej listy zadan
-- Wojciech Jedynak
-- Pawel Wieczorek

module ExercisesPaper where

  module MartinLof where
    -- Zakodowanie teorii typow Martina-Lof'a w Agdzie. Jest to zgodne z idea
    -- 'logical framework' o ktorej wspominalismy na seminarium. Agda to taki
    -- framework i posluzyl do zdefiniowania teorii.
    -- 
    -- Wyrazenia agdy to wyrazenia za pomoca ktorymi budujemy teorie
    --
    -- Roznice notacyjne:
    -- Podmiot                     Ksiazka         Teoria zakodowana w Agdzie
    --  aplikacja (wyrazenia)      f(x)            f x
    --  aplikacja (wyrazenia)      f(x,y,z)        f x y z
    --  abstrakcja (wyrazenia)     (x)e            λ x → e
    --  Konstruktor Π-typu         Π               Π (ten sam symbol)
    --  Π-typ                      (Π x ∈ A) B(x)  Π A B
    --  Π-typ                      (Π x ∈ A) B(x)  Π[ x ∶ A ] B
    --  Konstruktor Σ-typu         Σ               Σ (ten sam sysmbol)
    --  Σ-typ                      (Σ x ∈ A) B(x)  Σ A B
    --  Σ-typ                      (Σ x ∈ A) B(x)  Σ[ x ∶ A ] B
    --  kontruktor λ               λ               Λ 
    --  funkcja                    λ b             Λ b
    --  funkcja                    λx.b            Λ[ x ] b
    --  zwykla strzalka            →               ⇒ (NIE ten sam symbol)
    --  zwykla para                ×               × (ten sam symbol)
    --
    -- Notacje:
    --  Π A (λ x → e)          Π[ x ∶ A ] e
    --  Σ A (λ x → e)          Σ[ x ∶ A ] e
    --  Λ (λ x → e)            Λ[ x ] e

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

    apply' : { A : Set} → { B : A → Set }
          → Π A B → (x : A)
          → B x
    apply' (Λ f) x = f x

    syntax Π A (λ x → B) = Π[ x ∶ A ] B
    syntax Λ (λ x → e)   = Λ[ x ] e

    _⇒_ : Set → Set → Set
    A ⇒ B = Π A (λ x → B)

    funsplit : { A : Set } → {B : A → Set }
             → {C : Π A B  → Set }
             → ((b : (x : A) → B x ) → C (Λ b))
             → (f : Π A B) → C f
    funsplit H (Λ f) = H f

    apply : { A : Set} → { B : A → Set }
          → Π A B → (x : A)
          → B x
    apply f a = funsplit (λ b → b a) f

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

    ¬_ : Set → Set
    ¬ C = C ⇒ ⊥


  module Task1 where
    open MartinLof

    --
    -- Trudno sformalizowac nasze zadanie dotyczace dodania nowych regul
    -- do systemu poniewaz tutaj zalatwiaja nam duzo typy indukcyjne.
    -- Nadal mozna zweryfikowac regule eliminacji.
    --

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

    --
    -- Uniwersum ala Tarski
    --

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
    
    -- zrobione przy definicji teorii, ⊎


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


  module Task7 where
    open MartinLof
    open Task6

    --
    apply2 : {A : Set} {B : A → Set} → {C : (x : A) → B x → Set}
           → (Π[ x ∶ A ] Π[ b ∶ B x ] C x b)
           → (x : A) → (y : B x)
           → C x y
    apply2 f x y = apply (apply f x) y
    --

    add : ℕ ⇒ (ℕ ⇒ ℕ)
    add = Λ[ a ] Λ[ b ] natrec b (λ n r → succ r) a

    spec1 : Π[ a ∶ ℕ ] apply2 add O a ≡ a
    spec1 = Λ[ a ] id a

    spec2 : Π[ a ∶ ℕ ] apply2 add a O ≡ a
    spec2 = Λ[ a ] natrec
               {C = λ x → apply2 add x O ≡ x}
               (id O) (λ n H → cong H (Λ succ)) a

    spec3 : Π[ a ∶ ℕ ] Π[ b ∶ ℕ ] apply2 add (succ a) b ≡ succ (apply2 add a b)
    spec3 = Λ[ a ] Λ[ b ] natrec 
          {C = λ x → apply2 add (succ x) b ≡ succ (apply2 add x b)}
          (id (succ b)) 
          (λ n H → id (succ (apply2 add (succ n) b)))
          a

    spec4 : Π[ a ∶ ℕ ] Π[ b ∶ ℕ ] apply2 add a b ≡ apply2 add b a
    spec4 = Λ[ a ] natrec 
          {C = λ x → Π ℕ (λ b → apply2 add x b ≡ apply2 add b x)}
          (Λ[ b ] symm (apply spec2 b))
          (λ n H → Λ[ b ] {!!})
          a

  module Task8 where
    open MartinLof
    open Task6

    --
    -- Typem EQ nie mozemy sie posluzyc bo go nie mozna zdefiniowac.
    -- Nie mozna dodac do systemu nowej reguly wnioskowania (silnej eliminacji)
    --

    eta : {A : Set} {B : A → Set}
        → (f : Π A B)
        → f ≡ Λ (λ x → apply f x)
    eta f = funsplit
      {C = (λ g → g ≡ Λ (λ x → apply g x))} 
      (λ b → id (Λ b))
       f

  module Task9 where
    open MartinLof
    open Task6

    --
    -- Typem EQ nie mozemy sie posluzyc bo go nie mozna zdefiniowac.
    -- Nie mozna dodac do systemu nowej reguly wnioskowania (silnej eliminacji)
    --

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

    --
    -- Dowod jak w ksiazce, uzycie reguly Leibniza:
    -- 
    --   [0 = succ n] true     IsZero(0) true
    -- --------------------------------------
    --        IsZero(succ n) true
    --
    -- IsZero(succ n) = ⊥


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

    --
    -- Rozwiazanie:
    --
    -- 0 | f 0 0 | f 0 1 | ...
    -- 1 | f 1 0 | f 1 1 | ...
    --   | ...   
    -- n | ...           | f n n | ..
    --   | ...
    --
    -- Definiujemy nowy ciag taki aby jego n-ty element byl
    -- rozny od elementu (f n n) w powyzszej tabelce. Definiujemy
    -- ciag ktory jest negacja elementow przekatnej.
    --
    -- s n = negb (f n n)
    --
    -- Poniewaz to prawidlowy ciag binarny to ma swoj numerek
    -- h = g s
    -- taki ze f h = s  (mowi nam o tym zalozenie f (g s) = s)
    --
    -- Mamy paradoksalna rownosc dla ciagu s zaaplikowanego do swojego numeru:
    -- 
    -- s h = negb (f h h) = negb (f (g s) h) = negb (s h)
    -- widzimy ze definicja ciagu zanegowala swoja wlasna wartosc

    --
    -- Prawdziwe rozwiazanie:
    --
    -- Mamy udowodnic negacje, a wiec mamy stworzyc funkcje ktora daje
    -- absurdalna wartosc.
    -- W argumencie funkcji mamy funkcje 'f', funkcje 'g' 
    -- oraz dowod ze g jest prawa odwrotnoscia.
    -- Posluzmy sie makrem diagonal(f,g,Heq) ktore wezmie rozpakowane z Σ-typow
    -- wartosci.
    --
    -- Chcemy teraz uzyskac:
    --
    -- f ∈ ℕ → BinSeq
    -- g ∈ BinSeq → ℕ
    -- Heq ∈ (Π s ∈ BinSeq) [ s ≡ apply f (apply g s) ]
    -- -------------------------------------------------
    -- diagonal(f,g,Heq) ∈ ⊥
    --
    -- No wiec lecimy dokladnie jak w kartkowym dowodzie
    -- * definicja ciagu:
    -- s n ≣ apply(negb, (apply((apply(f,n),n))))
    --
    -- * jego numerek:
    -- h ≡ apply(g, s) ≡ apply (g,((n) apply(negb, (apply((apply(f,n),n))))))
    --
    -- * paradoksalna rownosc
    -- Niech P(x) ≡ apply(negb, (apply(x,h))) ≡  apply(negb, (apply(s,h)))
    --
    --  apply(Heq,s) ∈ [ s ≡ apply(f,(apply(g,s))) ]     id (...) ∈ P(s)
    -- ----------------------------------------------------------------------
    --   subst( apply(Heq,s), id (...)) ∈ P (apply(f,(apply(g,s))))
    --
    -- Niech thm ≡ subst( apply(Heq,s), id (...))
    -- Teraz, P (apply(f,(apply(g,s)))) oznacza 
    --        [apply(negb, (apply(s,h))) ≡ apply(s,h)]
    --
    -- Z poprzedniego zadania mamy Hnegb ∈ (Π b ∈ Bool) ¬ apply(negb,b) ≡ b
    -- a wiec diagonal(f,g,Heq) ≡ apply(apply(Hnegb,s(h)), thm) ∈ ⊥
    -- 
    -- Otrzymujemy ostatecznie:
    -- cantor = λH. split( (f,H') split( (g, Heq) diagonal(f,g,Heq), H'), H)


    cantor : ¬ (Σ[ f ∶ ℕ ⇒ BinSeq ] (Σ[ g ∶ BinSeq ⇒ ℕ ]
             Π[ s ∶ BinSeq ] s ≡ (apply f (apply g s))))
           
    cantor = Λ[ H ] split (λ f → split (λ g H0 → diagonal f g H0) ) H
      where
       diagonal : (f : ℕ ⇒ BinSeq) → (g : BinSeq ⇒ ℕ)
                → Π[ s ∶ BinSeq ] s ≡  (apply f (apply g s))
                → ⊥
       diagonal f g Heq = apply (apply Hnegb (apply s h)) thm2
         where
           s : BinSeq
           s = Λ[ n ] apply negb (apply (apply f n) n)

           h : ℕ
           h = apply g s

           thm2 :
                apply s h
                ≡
                apply negb (apply s h)

           thm2 = subst
                  {P = λ x → apply negb (apply x h) ≡ apply negb (apply s h)}
                  (apply Heq s) (id (apply negb (apply s h)))

