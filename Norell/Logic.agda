module Logic where
  open import Data.Bool
  open import Function

  record True : Set  where

  data False : Set where

  IsTrue : Bool → Set
  IsTrue true = True
  IsTrue false = False

  IsFalse : Bool → Set
  IsFalse = IsTrue ∘ not

