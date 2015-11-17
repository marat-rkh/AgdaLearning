module Ex34 where

open import Data.Nat
open import Data.String
open import Data.List hiding (_++_)

open import Logic
open import Ch3 using (All; _:all:_; all[])

-- Tag, Child and Schema represent XML (codes of the universe)
Tag = String

data Child : Set

data Schema : Set where
  tag : Tag → List Child → Schema

data Child where
  text : Child
  elem : ℕ → ℕ → Schema → Child

-- Additional data for decoding
-- BList is like Data.Fin
data BList (A : Set) : ℕ -> Set where
  [] : ∀ {n} -> BList A n
  _∷_ : ∀ {n} -> A -> BList A n -> BList A (suc n)

-- Pair
data Cons (A B : Set) : Set where
  _∷_ : A -> B -> Cons A B

-- List of size between n and m
FList : Set -> ℕ -> ℕ -> Set
FList A zero m = BList A m
FList A (suc n) zero = False
FList A (suc n) (suc m) = Cons A (FList A n m)

-- Decoding 
Element : Child → Set

data XML : Schema → Set where
  element : ∀ {kids} (t : Tag) → All Element kids → XML (tag t kids)

Element text = String
Element (elem n m s) = FList (XML s) n m

-- (a) Implement a function to print XML documents
printChildren : {kids : List Child} → All Element kids → String

printXML : {s : Schema} → XML s → String
printXML (element t allKids) = 
  "<" ++ t ++ ">\n" ++ 
  printChildren allKids ++ 
  "<\\" ++ t ++ ">\n"

printChild : {kid : Child} → Element kid → String
printChild {text} str = str
printChild {elem zero m s} [] = ""
printChild {elem zero (suc m) s} (b ∷ bs) = printXML b ++ printChild {elem zero m s} bs
printChild {elem (suc n) zero s} ()
printChild {elem (suc n) (suc m) s} (xml ∷ flist) = printXML xml ++ printChild {elem n m s} flist

printChildren all[] = "" 
printChildren {k ∷ _} (e :all: es) = printChild {k} e ++ printChildren es
