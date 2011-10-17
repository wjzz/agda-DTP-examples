{-# LANGUAGE GADTs #-}

module Main where

data Color where
  Reg   :: Color
  Green :: Color
  Blue  :: Color
  
data List a where
  Nil  :: List a
  Cons :: a -> List a -> List a