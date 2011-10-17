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


\section{Typ identycznościowy, czyli równość w języku}

\begin{code}

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()


¬_ : Set → Set
¬ A = A → ⊥

infix 5 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

\end{code}

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

W Haskellu bardzo często używamy funkcji zip, która jest zdefiniowana następująco: \\
\\
zip :: [a] -> [b] -> [(a,b)] \\
zip (x:xs) (y:ys) = (x,y) : zip xs ys \\
zip \_ \_ = [] \\

Jak widać, przyjęto tutaj, że jeśli listy są różnej długości, to dłuższa lista jest ucinana.
Nie zawsze takie rozwiązanie jest satysfakcjonujące. Wymyśl taką sygnaturę dla funkcji zip na wektorach,
aby niedopuścić (statycznie, za pomocą systemu typów) do niebezpiecznych wywołań.

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


\end{document}
