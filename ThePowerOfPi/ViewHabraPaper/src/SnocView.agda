module SnocView where

open import Data.Nat

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A
infixr 5 _::_ 

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data SnocView {A : Set} : List A -> Set where
  [] : SnocView []
  _:::_ : (xs : List A) -> (x : A) -> SnocView (xs ++ (x :: []))

sx : SnocView (1 :: 2 :: 3 :: [])
sx = (1 :: 2 :: []) ::: 3

snocView : {A : Set} -> (xs : List A) -> SnocView xs
snocView [] = []
snocView (x :: xs)              with snocView xs
snocView (x :: .[])                | []       = [] ::: x
snocView (x :: .(ys ++ (y :: []))) | ys ::: y = (x :: ys) ::: y

rotateRight : {A : Set} -> List A -> List A
rotateRight xs with snocView xs
rotateRight ._ | [] = []
rotateRight ._ | ys ::: y = y :: ys
