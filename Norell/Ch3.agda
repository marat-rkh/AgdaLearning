-- Views
module Ch3 where

-- Natural number parity 
open import Data.Nat

data Parity : ℕ -> Set where
  even : (k : ℕ) -> Parity (k * 2)
  odd : (k : ℕ) -> Parity (1 + k * 2)

parity : (n : ℕ) -> Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

half : ℕ -> ℕ
half n with parity n
half .(k * 2) | even k = k
half .(1 + k * 2) | odd k = k


-- Finding an element in a list
open import Function
open import Data.List using (List; _∷_; []; filter; _++_; length)
open import Data.Bool
open import Logic
open import Relation.Binary.PropositionalEquality
open import Data.Unit 

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[] : All P []
  _:all:_ : ∀ {x xs} -> P x -> All P xs -> All P (x ∷ xs)

satisfies : {A : Set} -> (A -> Bool) -> A -> Set
satisfies p x = IsTrue (p x)

-- additional views
data EqualsTo {A : Set}(x : A) : Set where
  equalsTo : (y : A) → x ≡ y → EqualsTo x

inspectEquals : {A : Set}(x : A) → EqualsTo x
inspectEquals x = equalsTo x refl

trueIsTrue : {x : Bool} → x ≡ true → IsTrue x
trueIsTrue refl = _

falseIsFalse : {x : Bool} -> x ≡ false -> IsFalse x
falseIsFalse refl = _

-- lem-filer-sat - hard way
lem-filter-sat : {A : Set}(p : A → Bool) → (xs : List A) → All (satisfies p) (filter p xs)
lem-filter-sat p [] = all[]
lem-filter-sat p (x ∷ xs) with inspectEquals (p x)
lem-filter-sat p (x ∷ xs) | equalsTo y eqProof with p x | eqProof
lem-filter-sat p (x ∷ xs) | equalsTo true eqProof | .true | refl = trueIsTrue eqProof :all: lem-filter-sat p xs
lem-filter-sat p (x ∷ xs) | equalsTo false eqProof | .false | refl = lem-filter-sat p xs

-- lem-filter-sat - simpler way
lem-filter-sat2 : {A : Set}(p : A → Bool) → (xs : List A) → All (satisfies p) (filter p xs)
lem-filter-sat2 p [] = all[]
lem-filter-sat2 p (x ∷ xs) with p x | inspect p x
... | true | [ eqProof ] = trueIsTrue eqProof :all: (lem-filter-sat2 p xs) 
... | false | _  = (lem-filter-sat2 p xs)

data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : forall {xs} → All (satisfies (not ∘ p)) xs → Find p xs

find : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspectEquals (p x)
... | equalsTo true prf = found [] x (trueIsTrue prf) xs
... | equalsTo false prf with find p xs
find p (x ∷ ._) | equalsTo false _ | found xs y py ys = found (x ∷ xs) y py ys
find p (x ∷ xs) | equalsTo false prf | not-found npxs = not-found (falseIsFalse prf :all: npxs)


-- Indexing into a list
data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ (x ∷ xs)
  tl : forall {y xs} -> x ∈ xs -> x ∈ (y ∷ xs)

index : forall {A}{x : A}{xs} -> x ∈ xs -> ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ -> Set where
  inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : ℕ) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) -> Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + n) | outside n = outside n
