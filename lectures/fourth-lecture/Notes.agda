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
  just    : A → Maybe A

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

plus : Nat -> Nat -> Nat
plus zero    m = m
plus (suc n) m = suc (plus n m)

nat-test : Nat
nat-test = plus (suc (suc zero)) (suc zero)

-- listy 

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

length : (A : Set) → List A → Nat
length A l = {!!}

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