-- To jest komentarz jednolinijkowy

{- To jest komentarz wielowierszowy.

Ten plik omawia podstawy Agdy i różnice między Agdą a Haskellem.

Tutaj sie kończy. 
-}

--------------------
--  Wprowadzenie  --
--------------------

{-
Każdy plik źródłowy w Agdzie musi:
- mieć rozszerzenie .agda (ew. .lagda, jeśli chcemy używać stylu literackiego)
- rozpoczynać się od deklaracji 
module NAZWA where
  [o ile sam plik nazywa się NAZWA.agda (wielkość znaków ma znaczenie)]
-}

module Notes where

{- W przeciwieństwie do Haskella, nie mamy automatycznie importowanego preludium
  standardowego w Agdzie. W związku z tym, w tym miejscu w pliku nie mamy 
  dostępu do *prawie* żadnego wbudowanego typu.

  Zagadka 1: dlaczego prawie? [rozwiązanie na końcu pliku]
-}

---------------------------------------
--  Definiowanie typów indukcyjnych  --
---------------------------------------

{- W Haskellu piszemy np.
data Color = Red | Green | Blue

Po włączeniu rozszerzenia GADT, możemy w wielu implementacjach napisać
data Color where
  Reg   :: Color
  Green :: Color
  Blue  :: Color

W Agdzie używamy wyłącznie stylu GADT, z dwoma różnicami 
  * piszemy : (dwukropek) zamiast :: (dwóch dwukropków) w deklaracjach typów
  * przed słowem 'where' musimy podać typ właśnie deklarowanego typu (czyli rodzaj [ang. kind]).
    W naszych pierwszych przykładach rodzajem będzie zawsze Set (pierwsze uniwersum, zbiór małych zbiorów)

Jesteśmy juz gotowi do zdefiniowania naszego pierwszego typu indukcyjnego w Agdzie! :-)

-}

-- 1. Typy wyliczeniowe

data Color : Set where
  red   : Color
  green : Color
  blue  : Color

-- W tym wypadku możemy zastosować skrót:

data Color2 : Set where
  red green blue : Color2

{- Uwaga leksykalna

W Haskellu mamy wymaganie, żeby nazwy typów i konstruktorów zaczynały się WIELKĄ literą.
W Agdzie nie ma takiej dyscypliny. Wydaje się, że najcześciej (np. w bibliotece std)
używa sie konwencji typy - wielką literą, konstruktory - małą literą.

-}

-- Taka deklaracja jest więc także OK:

data color : Set where
  Red Green Blue : color


-- 2. Konstuktory biorące argumenty

{- Spróbujmy zdefiniować typ Maybe z Haskella (w kręgach MLowych znany jako OPTION).
  Możemy oczywiście zdefiniować wersję dla naszego konkretnego typu kolor: 
-}

data MaybeColor : Set where
  nothing : MaybeColor
  just    : Color -> MaybeColor

{- W tym wypadku nothing jest konstruktorem zero-arnym, 
   just z kolei bierze jeden argument typy Color.

  Możemy zdefiniować przykładową wartość typu MaybeColor: -}

maybeColorExample : MaybeColor
maybeColorExample = just red

-- 3. Typy parametryzowane

{- Co jeśli chcemy zdefiniować prawdziwy typ Maybe, czyli działający dla dowolnego typu?
   Wystarczy naszą definicję sparametryzować dowolnym elementem ze zbioru Set: 
-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

-- nasza definicja działa z dowolnym typem, w szczególności z typem Maybe

maybeExample : Maybe Color
maybeExample = nothing

maybeExample2 : Maybe Color
maybeExample2 = just red

-- 4. Definicje rekurencyjne

-- liczby naturalne

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- magiczna deklaracja, która pozwala nam pisać literały naturalne, 
-- np. 3 zamiast suc (suc (suc zero))

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

natLiteral : Nat
natLiteral = 42


plus : Nat -> Nat -> Nat
plus zero    m = m
plus (suc n) m = suc (plus n m)

nat-test : Nat
nat-test = plus (suc (suc zero)) (suc zero)

-- listy 

data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

length : (A : Set) -> List A -> Nat
length A l = {!!}

-- 5. typy indeksowane wartościami

-- wektory, czyli listy, które mają w typie zapisaną swoją długość

data Vec (A : Set) : Nat -> Set where
  vnil  : Vec A zero
  vcons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)

{-
uwagi: 
* Wyrażenie Vec (A : Set) : Nat -> Set oznacza, że
  samo Vec A nie jest jeszcze typem. 
  Dopiero Vec A n, dla n : Nat jest typem.
* pierwszy konstuktor mówi, że wektor pusty jest wektorem długości 0
* drugi konstuktor mówi, że jeśli mamy wartość typu A oraz 
  wektorów elementów typu A długości n, to możemy utworzyć wektor długości 1+n
-}

-- przykładowe wektory

emptyVec : Vec Nat zero
emptyVec = vnil

twoNats : Vec Nat (suc (suc zero))
twoNats = vcons (suc zero) 42 (vcons zero 107 vnil)

-- konkatenacja wektorów

vappend : (A : Set) -> (n m : Nat) -> Vec A n -> Vec A m -> Vec A (plus n m)
vappend A .0       m vnil           v2 = v2
vappend A .(suc n) m (vcons n a v1) v2 = vcons _ a (vappend A _ _ v1 v2)

-- TODO
-- wyjaśnić znaczenie kropek i podkreśleń -> najlepiej napisać kilka wersji

-- Zauważmy, że pierwsze trzy argumenty vappend można wywnioskować z pozostałych.
-- W takich sytuacjach możemy użyć argumentów niejawnych.
-- Zamiast (A : Set) -> .. wystarczy napisać {A : Set} -> ..

vappendImplicit : {A : Set} -> {n m : Nat} -> Vec A n -> Vec A m -> Vec A (plus n m)
vappendImplicit vnil                   v2 = v2
vappendImplicit {m = m} (vcons n x v1) v2 = vcons (plus n m) x (vappendImplicit v1 v2)

--vappendImplicit (vcons n x v1) v2 = vcons _ x (vappendImplicit v1 v2)

{- W przykładzie wyżej mieliśmy mały kłopot: jak odwołać się do argumentu niejawnego?
  Pierwszy sposób polega na użyciu składni {NAZWA_Z_SYGNATURY = NAZWA_KTÓRĄ_CHCEMY_UŻYĆ}.
  Drugi sposob (a tutaj właściwie sztuczka) to podanie _ w miejscu, w którym chcemy użyć
  zmiennej, której nie została jawnie nazwana. 
  (Agda oznacza takie zmienne w trybie interaktywnym poprzez dodanie kropki na poczatku).
  Pokreślenie oznacza "wykombinuj automatycznie [poprzez unifikację] jaki tutaj musi być term".
-}

{- W przykładach z wektorami problem pojawia się, gdyż musimy w konstuktorze vcons podać
   długość wektora, który rozszerzamy. Tak naprawdę, to ta wartość także może być bez
   problemu wydedukowana!

   W praktyce używamy więc zawsze tak zdefiniowanych wektorów:
-}

data Vector (A : Set) : Nat -> Set where
  vec-nil  : Vector A zero
  vec-cons : {n : Nat} -> (x : A) -> (xs : Vector A n) -> Vector A (suc n)

{- Dlaczego daliśmy nazwy x oraz xs, mimo że ich nie używamy?

  Tzn. dlaczego nie napisaliśmy po prostu
  vec-cons : {n : Nat} -> A -> Vector A n -> Vector A (suc n)
  ?

  Ta zmiana ma tylko znaczenie przy interacji. Jeśli podamy nasze nazwy, to Agda
  będzie starać się ich używać podczas automatycznego generowania kodu.
  Bez podania naszych propozycji dostaniemy nazwy postaci np. y y' y2 y3 ...
-}

-- do końca tych notatek będziemy jednak dla spójności używać typu Vec.


-- odwracanie wektora (naiwnie)

 -- rev (x : xs) = rev xs ++ [x]

vreverse : (A : Set) -> (n : Nat) -> Vec A n -> Vec A n
vreverse A .0       vnil          = vnil
vreverse A .(suc n) (vcons n a v) = {! vappend _ _ _ (vreverse _ _ v) (vcons _ a vnil) !}

{- Mamy problem!
    Agda oczekuje wyrażenia typu Vec A (1 + n),
  my zaś podajemy wyrażenie typu Vec A (n + 1) _!

  Pytanie: Ale zaraz... przecież w arytmetyce 1+n=n+1, więc w czym problem?
           Mieliśmy przecież w teorii typów Martina-Lôfa sądy postaci:
            jeśli N = M to Vec A N = Vec A M.

  Odpowiedź: Problem jest taki, że Agda zna tylko tyle arytmetyki 
    (ogólniej: wiedzy o bytach, które w niej definiujemy), ile ją nauczymy.

  Musimy więc najpierw nauczyć się dowodzić praw matematycznych.
-}  
  
----------------------------------------------------
--  Typ identycznościowy, czyli równość w Agdzie  --
----------------------------------------------------

data _==_ {A : Set} : A -> A -> Set where
  refl : {a : A} → a == a

symm : {A : Set} -> (a b : A) -> a == b -> b == a
symm .b b refl = refl

subst : {A : Set} -> (P : A -> Set) -> (a b : A) -> a == b -> P a -> P b
subst P a .a refl Pa = Pa

-- przykład zastosowania subst: wektory równych typow

listsEq : (A : Set) -> (n m : Nat) -> n == m -> Vec A n -> Vec A m
listsEq A n m eq v = subst (λ x → Vec A x) n m eq v

-- możemy tutaj poradzić sobie bezpośrednio robiąc pattern matching na dowodzenie równości
-- czy jakby wklejajac dowod subst

listsEqDirect : {A : Set} -> (n m : Nat) -> n == m -> Vec A n -> Vec A m
listsEqDirect .m m refl Vn = Vn

---------------
--  Negacja  --
---------------

-- Założmy, że chcemy udowodnić, że 0 != 1, czyli ¬ (0 == 1).
-- Jak zdefiniować negację? Jak zdefiniować fałsz?

-- Izomorfizm Curry'ego-Howarda mówi, że fałsz odpowiada typowi pustemu.

data Bottom : Set where

-- brak konstruktorów => typ jest pusty!

-- możemy udowodnić prawo: 
--  logika:        z fałszu wynika wszystko
--  programowanie: jeśli istnieje wartość typu pustego, to istnieje wartość dowolnego typu

bottom-elim : (A : Set) -> Bottom -> A
bottom-elim A ()

-- napis () oznacza: "ten wzorzec nie ma sensu, gdyż ten typ jest _w_oczywisty_sposob_ pusty.
-- nikt nigdy nie utworzy wartości takiego typu, więc nie musze nawet definiowac prawej strony"

-- przykład

stupid : Bottom -> 2 == 3
stupid ()

-- ciekawostka

soEasy : 0 == 1 -> Bottom
soEasy ()

-- Agda widzi, że 0 i 1 nie są konwertowalne, więc 0 == 1 musi być pusty!

-- negacja
-- Negację definiujemy zgodnie z ICH, jako funkcje do typu pustego:

~_ : Set -> Set                         -- definiujemy operator prefixowy
~ A = A -> Bottom

------------------------------
--  Rozwiązanie zagadki 1.  --
------------------------------

{- Nawet w pustym pliku Agdowym mamy dostęp do dwu wbudowanych rodzajów bytów:
  * operator przestrzeni funkcyjnej -> (unikodowo: → (wpisujemy \->))
  * zbiory Set (= Set0 = Set₀), Set1, Set2, ..., które tworzą hierarchię
-}

-- parę przykładów

solution1 : Set → Set
solution1 x = x

solution2 : (A : Set1) → Set1
solution2 x = x

solution1-01 : Set1
solution1-01 = Set

solution1-12 : Set2
solution1-12 = Set1

-- To nie działa. Uniwersa w Agdzie nie są kumulatywne
{-
solution1-02 : Set2
solution1-02 = Set
-}

-- dopóki nie zdefiniujemy jakiegoś typu indukcyjnego, typ Set jest... pusty!
hmm : Set
hmm = {!!}
