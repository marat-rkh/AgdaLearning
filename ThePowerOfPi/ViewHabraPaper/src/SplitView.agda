module SplitView where

open import Data.Nat renaming (ℕ to Nat; zero to Zero; suc to Suc)

-- Vector --
data Vec (A : Set) : Nat -> Set where
  [] : Vec A Zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (Suc n)
infixr 5 _::_

v1 : Vec Nat 2
v1 = 1 :: (2 :: [])

-- broken : Vec Nat 3
-- broken = 1 :: (2 :: [])

_++_ : forall {A m n} -> Vec A m -> Vec A n -> Vec A (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

take : forall {A m} -> (n : Nat) -> Vec A (n + m) -> Vec A n
take Zero l = []
take (Suc k) (x :: xs) = x :: take k xs

drop : forall {A m} -> (n : Nat) -> Vec A (n + m) -> Vec A m
drop Zero xs = xs
drop (Suc k) (x :: xs) = drop k xs

-- Word -- 
data Bit : Set where
  O : Bit
  I : Bit

Word : Nat -> Set
Word n = Vec Bit n

-- Patten matching on Refl --
data _==_ {A : Set} : A -> A -> Set where
  Refl : {x : A} -> x == x

eq : (3 == 3)
eq = Refl

notEq : (3 == 4)
notEq = {!!}

f : (x : Nat) -> (y : Nat) -> (x == y) -> Nat
f x .x Refl = x

-- SplitView --
split : forall {A} -> (n : Nat) -> (m : Nat) -> Vec A (m * n) -> Vec (Vec A n) m
split n Zero [] = []
split n (Suc k) xs = (take n xs) :: (split n k (drop n xs))

concat : forall {A n m } -> Vec (Vec A n) m -> Vec A (m * n)
concat [] = []
concat (xs :: xss) = xs ++ concat xss

data SplitView {A : Set} : {n : Nat} -> (m : Nat) -> Vec A (m * n) -> Set where
  [_] : forall {m n} -> (xss : Vec (Vec A n) m) -> SplitView m (concat xss)

-- splitView1 : {A : Set} -> (n : Nat) -> (m : Nat) -> (xs : Vec A (m * n)) -> SplitView m xs
-- splitView1 n m xs = [ split n m xs ]

splitView2 : {A : Set} -> (n : Nat) -> (m : Nat) -> (xs : Vec A (m * n)) -> SplitView m xs
splitView2 n m xs with [ split n m xs ]
splitView2 n m xs | v = {!!}

splitView3 : {A : Set} -> (n : Nat) -> (m : Nat) -> (xs : Vec A (m * n)) -> SplitView m xs
splitView3 n m xs with concat (split n m xs) | [ split n m xs ]
splitView3 n m xs | ys | v = {!!}

takeDropLemma : ∀ {A : Set} {n m} →  (xs : Vec A (n + m)) →  ((take n xs) ++ (drop n xs)) == xs
takeDropLemma {n = 0} _ = Refl
takeDropLemma {n = Suc k} (x :: xs) with ((take k xs) ++ (drop k xs)) | takeDropLemma {n = k} xs
takeDropLemma {n = Suc k} (x :: xs) | ._ | Refl = Refl

splitConcatLemma : ∀ {A} -> (n : Nat) -> (m : Nat) -> (xs : Vec A (m * n)) -> concat (split n m xs) == xs
splitConcatLemma _ 0 [] = Refl
splitConcatLemma n (Suc k) xs with concat (split n k (drop n xs)) | splitConcatLemma n k (drop n xs)
splitConcatLemma n (Suc k) xs | ._ | Refl = takeDropLemma {n = n} {m = k * n} xs

splitView4 : {A : Set} -> (n : Nat) -> (m : Nat) -> (xs : Vec A (m * n)) -> SplitView m xs
splitView4 n m xs with concat (split n m xs) | [ split n m xs ] | splitConcatLemma n m xs
splitView4 n m xs | ys | v | eq = {!!}

splitView : {A : Set} -> (n : Nat) -> (m : Nat) -> (xs : Vec A (m * n)) -> SplitView m xs
splitView n m xs with concat (split n m xs) | [ split n m xs ] | splitConcatLemma n m xs
splitView n m xs | .xs | v | Refl = v

swapAB : Word 32 -> Word 32
swapAB xs with splitView 8 4 xs
swapAB ._ | [ a :: b :: c :: d :: [] ] = concat (b :: a :: c :: d :: [])
