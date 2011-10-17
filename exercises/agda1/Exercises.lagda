\documentclass{scrartcl}

% current annoyance: this will be fixed
% by the next update of agda.fmt
\def\textmu{}

%include agda.fmt

%format not = "not"

\usepackage[T1]{fontenc}
% \usepackage[utf8]{inputenc} 
\usepackage[polish]{babel} 

\newtheorem{zadanie}{Zadanie}

\author{Wojciech Jedynak \and Paweł Wieczorek}
\title{Ćwiczenia z Agdy - Lista 1.}

\begin{document}

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
Udowodnij następująca własności dodawania:

\begin{code}
plus-right-zero : (n : ℕ) → n + 0 ≡ n
plus-right-zero = {!!}

plus-suc-n-m : (n m : ℕ) → suc (n + m) ≡ n + suc m
plus-suc-n-m = {!!}
\end{code}

\end{zadanie}

\begin{zadanie}
Korzystając z poprzedniego zadania, udowodnij przemienność dodawania:
(pamiętaj, że wg ICH indukcja = rekursja!)

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

\end{document}
