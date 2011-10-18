\documentclass{scrartcl}

% current annoyance: this will be fixed
% by the next update of agda.fmt
\def\textmu{}

%include agda.fmt

%format not = "not"

\usepackage[T1]{fontenc}
% \usepackage[utf8]{inputenc} 
\usepackage[polish]{babel} 
\usepackage{listings}

\newtheorem{zadanie}{Zadanie}

\author{Wojciech Jedynak \and Paweł Wieczorek}
\title{Ćwiczenia z Agdy - Lista 1.}

\begin{document}
\lstset{language=Haskell}

\maketitle

\begin{code}
module Exercises where

\end{code}

\section{Podstawy Izomorfizmu Curry'ego-Howarda}

Fałsz zdefiniowaliśmy w Agdzie jako typ pusty:

\begin{code}

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

\end{code}

Możemy teraz wyrazić negację w standardowy sposób: jako funkcję w zbiór pusty.

\begin{code}

¬_ : Set → Set
¬ A = A → ⊥

\end{code}

\begin{zadanie}
Udowodnij, że p ⇒ ¬¬p, czyli dokończ poniższą definicję:

\begin{code}
pnnp : {A : Set} → A → ¬ ¬ A
pnnp = {!!}
\end{code}

Czy potrafisz udowodnić implikację w drugą stronę?

\end{zadanie}

\begin{zadanie}

Udowodnij prawo kontrapozycji, czyli pokaż że (A ⇒ B) ⇒ (¬ B ⇒ ¬ A). Czy potrafisz udowodnić twierdzenie odwrotne?

\end{zadanie}

\begin{zadanie}

Zdefiniuj typ, który będzie odpowiadał formule atomowej ⊤. Jakiemu typowi z języków programowania on odpowiada?

\end{zadanie}

\begin{zadanie}

Polimorficzne pary, czyli odpowiednik koniukcji możemy zdefiniować następująco:

\begin{code}

data _∧_ (A B : Set) : Set where
  pair : (a : A) → (b : B) → A ∧ B

\end{code}

Udowodnij reguły eliminacji oraz prawo przemienności tj. zdefiniuj funkcje fst, snd i swap:

\begin{code}

fst : {A B : Set} → A ∧ B → A
fst = {!!}

snd : {A B : Set} → A ∧ B → B
snd = {!!}

swap : {A B : Set} → A ∧ B → B ∧ A
swap = {!!}

\end{code}

\end{zadanie}

\begin{zadanie}

Zdefiniuj typ sumy rozłącznej (czyli Haskellowy typ Either). Jakiemu spójnikowi logicznemu
odpowiada ten typ? Udowodnij przemienność tego spójnika.

\end{zadanie}

\begin{zadanie}

Korzystając z typów z poprzednich dwóch zadań, sformułuj i spróbuj udowodnić prawa deMorgana znane
z logiki klasycznej. Które z nich zachodzą w logice kostruktywnej?

\end{zadanie}


\section{Typ identycznościowy, czyli równość w języku}

Aby wydawać i dowodzić sądy o równości różnych bytów, zdefiniowaliśmy tzw. typ identycznościowy.
Typ ustalonych a,b ∈ A, a ≡ b jest zamieszkały wtw, gdy a i b obliczają się do tego samego
elementu kanonicznego (wartości).

\begin{code}

infix 5 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a


\end{code}

Różność elementów definiujemy jako... zaprzeczenie równości:

\begin{code}

_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

\end{code}

\begin{zadanie}

Pokazaliśmy już jak udowodnić niektóre właśności równości:

\begin{code}

symm : {A : Set} → (a b : A) → a ≡ b → b ≡ a
symm a .a refl = refl

subst : {A : Set} → (P : A → Set) → (a b : A) → a ≡ b → P a → P b
subst P a .a refl Pa = Pa

\end{code}

Udowodnij dwie dodatkowe (bardzo przydatne) właśności:

\begin{code}

trans : {A : Set} → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans = {!!} 

cong : {A B : Set} → (P : A → B) → (a b : A) → a ≡ b → P a ≡ P b
cong = {!!}

\end{code}


\end{zadanie}


\section{Wartości boolowskie}

Wartości boolowskie zdefiniowaliśmy następująco:

\begin{code}

data Bool : Set where
  false : Bool
  true  : Bool

\end{code}

\begin{zadanie}

Uzupełnij poniższą definicję tak, aby otrzymać funkcję negacji boolowskiej.

\begin{code}

not : Bool → Bool
not false = {!!}
not true  = {!!}

\end{code}

Udowodnij, że Twoja definicja spełnia następujące własności:

\begin{code}

not-has-no-fixed-points : (b : Bool) → not b ≢ b
not-has-no-fixed-points = {!!}

not-is-involutive : (b : Bool) → not (not b) ≡ b
not-is-involutive = {!!}

\end{code}



\end{zadanie}

\section{Liczby naturalne}

Na wykładzie zdefiniowaliśmy liczby naturalne z dodawaniem następująco:

\begin{code}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

infix 6 _+_ 

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

\end{code}

\begin{zadanie}
Pamiętając, że wg ICH indukcja = rekursja, udowodnij następujące własności dodawania:

\begin{code}
plus-right-zero : (n : ℕ) → n + 0 ≡ n
plus-right-zero = {!!}

plus-suc-n-m : (n m : ℕ) → suc (n + m) ≡ n + suc m
plus-suc-n-m = {!!}
\end{code}

\end{zadanie}

\begin{zadanie}
Korzystając z poprzedniego zadania, udowodnij przemienność dodawania:

\begin{code}
plus-commutative : (n m : ℕ) → n + m ≡ m + n
plus-commutative = {!!}
\end{code}

\end{zadanie}


\begin{zadanie}
Zdefiniuj mnożenie i potęgowanie dla liczb naturalnych.

\begin{code}
infix 7 _*_
infix 8 _^_

_*_ : ℕ → ℕ → ℕ
n * m = {!!}

_^_ : ℕ → ℕ → ℕ
n ^ m = {!!}         -- tutaj też ma być daszek :-)

\end{code}

Jeśli masz ochotę, to udowodnij przemienność mnożenia.

\end{zadanie}

\begin{zadanie}

Udowodnij, że zero ≢ suc (zero).

\end{zadanie}

\begin{zadanie}

Udowodnij następującą własność ("prawo skracania"):

\begin{code}

strip-suc : (n m : ℕ) → suc n ≡ suc m → n ≡ m
strip-suc = {!!}

\end{code}


\end{zadanie}



\section{Wektory}

Przypomnijmy definicję wektorów:

\begin{code}

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → (x : A) → (xs : Vec A n) → Vec A (suc n)

\end{code}

Zdefiniowaliśmy już m.in. konkatenację wektorów:

\begin{code}

_++_ : {A : Set} → {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ v2 = v2
(x ∷ v1) ++ v2 = x ∷ (v1 ++ v2)

\end{code}

\begin{zadanie}

Zaprogramuj funkcje vmap, która jest wektorowym odpowiednikiem map dla list.
Jaka powinna być długość wynikowego wektora?

\end{zadanie}

\begin{zadanie}

W Haskellu bardzo często używamy funkcji zip, która jest zdefiniowana następująco: \\
\\
zip :: [a] -> [b] -> [(a,b)] \\
zip (x:xs) (y:ys) = (x,y) : zip xs ys \\
zip \_ \_ = [] \\

Jak widać, przyjęto tutaj, że jeśli listy są różnej długości, to dłuższa lista jest ucinana.
Nie zawsze takie rozwiązanie jest satysfakcjonujące. Wymyśl taką sygnaturę dla funkcji zip na wektorach,
aby nie dopuścić (statycznie, za pomocą systemu typów) do niebezpiecznych wywołań.

\end{zadanie}

\begin{zadanie}

Zaprogramuj wydajną funkcję odwracającą wektor. Użyj funkcji subst, jeśli będziesz chcieć zmusić Agdę do stosowania praw arytmetyki.

\begin{code}

\end{code}


\end{zadanie}

\section{Zbiory skończone - typ fin}

Przypomnijmy definicję typu fin:

\begin{code}
data Fin : ℕ → Set where
  zero  : {n : ℕ} → Fin (suc n)
  suc   : {n : ℕ} → (i : Fin n) → Fin (suc n)

\end{code}

Dla dowolnego n ∈ ℕ typ Fin n ma dokładnie n mieszkańców (w szczególności Fin 0 jest pusty).
Własność ta sprawia, że typ Fin świetnie nadaje się do indeksowania wektorów.
Indeksowanie to jest bezpieczne, gdyż system typów wyklucza nam możliwość stworzenia indeksu, 
który wykraczałby poza dozwolony zakres.

\begin{code}

_!_ : {A : Set} {n : ℕ} → Vec A n → Fin n → A
[] ! ()
(x ∷ xs) ! zero  = x
(x ∷ xs) ! suc i = xs ! i

\end{code}

\begin{zadanie}

Zauważ, że typ Fin przypomina strukturą liczby naturalne, choć zawiera więcej informacji. \\
Napisz funkcję konwersji, która ''zapomina'' te dodatkowe informacje.

Np. jeśli Fin 2 = \{ 0₂, 1₂ \}, to chcemy mieć \\
toℕ 0₂ ≡ 0 \\
toℕ 1₂ ≡ 1 \\

\begin{code}
toℕ : {n : ℕ} → Fin n → ℕ
toℕ = {!!}
\end{code}

\end{zadanie}

\begin{zadanie}

Napisz funkcje, która dla danego n, zwraca największy element zbioru Fin (suc n).
Przez największy rozumiemy tutaj ten element, który jest zbudowany z największej
liczby konstruktorów.
\\
Przykładowo, dla n ≡ 3 mamy Fin 3 ≡ \{ 0₃, 1₃, 2₃ \} i jako wynik chcemy otrzymać 2₃.

\begin{code}
fmax : (n : ℕ) → Fin (suc n)
fmax = {!!}

\end{code}

\end{zadanie}

\begin{zadanie}

Jeśli udało Ci się zrobić poprzednie dwa zadania, to pokaż, że ich złozenie w jedną ze stron daje identyczność.
Czy potrafisz sformułować twierdzenie o złożeniu w drugą stronę?

\begin{code}
lemma-max : (n : ℕ) → toℕ (fmax n) ≡ n
lemma-max = {!!}

\end{code}

\end{zadanie}

\begin{zadanie}

W matematyce mamy \{ 0, 1, 2, .. n-1 \} ⊆ \{ 0, 1, 2, .. n-1, n \}.
Zainspirowani tym zawieraniem chcemy teraz
pokazać, że typ Fin n można osadzić w Fin (suc n). \\
Uwaga. Jednym ze sposobów byłoby po prostu użycie konstruktora suc, 
ale chcemy zrobić odwzorowanie, w którym $ k_n $ przechodzi na $ k_{n+1} $.

\begin{code}
fweak : {n : ℕ} → Fin n → Fin (suc n)
fweak = {!!}
\end{code}

Po zdefiniowaniu funkcji udowodnij jej poprawność:

\begin{code}
fweak-correctness : {n : ℕ} → (i : Fin n) → toℕ i ≡ toℕ (fweak i)
fweak-correctness = {!!}
\end{code}


\end{zadanie}

\begin{zadanie}
Pokaż, że dla każdego n ∈ ℕ, możemy stablicować wszystkie elementy
typu Fin n w n-elementowym wektorze.

\begin{code}
tabFins : (n : ℕ) → Vec (Fin n) n
tabFins = {!!}
\end{code}

\end{zadanie}

\end{document}
