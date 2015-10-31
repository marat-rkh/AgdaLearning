module Ex23 where
  open import Data.List 
  open import Data.Nat
  open import Data.Bool

  data _⊆_ {A : Set} : List A -> List A -> Set where
    subEmp : [] ⊆ []
    subDrop : ∀ {x xs ys} -> xs ⊆ ys -> xs ⊆ (x ∷ ys)
    subKeep : ∀ {x xs ys} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

  ⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
  ⊆-refl {xs = []} = subEmp
  ⊆-refl {xs = (y ∷ ys)} = subKeep ⊆-refl

  ⊆-trans : {A : Set}{xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans subEmp      q           = q
  ⊆-trans p           (subDrop b) = subDrop (⊆-trans p b) 
  ⊆-trans (subDrop a) (subKeep b) = subDrop (⊆-trans a b)
  ⊆-trans (subKeep a) (subKeep b) = subKeep (⊆-trans a b) 

  infixr 30 _∥_
  data SubList {A : Set} : List A -> Set where
    [] : SubList []
    _∥_ : ∀ x {xs} -> SubList xs -> SubList (x ∷ xs)
    skip : ∀ {x xs} -> SubList xs -> SubList (x ∷ xs)

  -- Define a function to extract the list corresponding to a sublist.
  forget : {A : Set}{xs : List A} -> SubList xs -> List A
  forget [] = []
  forget (x ∥ xsSub) = x ∷ (forget xsSub)
  forget (skip s) = forget s

  -- Now, prove that a SubList is a sublist in the sense of ⊆
  lem-forget : {A : Set}{xs : List A}(zs : SubList xs) → forget zs ⊆ xs
  lem-forget [] = subEmp
  lem-forget (x ∥ ys) = subKeep (lem-forget ys)
  lem-forget {_} {.x ∷ .xs} (skip {x} {xs} zs) = subDrop (lem-forget zs)

  -- Give an alternative definition of filter which satisfies the sublist property by construction.
  filterSub : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
  filterSub p [] = []
  filterSub p (x ∷ xs) with p x
  ... | true = x ∥ filterSub p xs 
  ... | false = skip (filterSub p xs)

  --  Define the complement of a sublist
  complement : {A : Set}{xs : List A} -> SubList xs -> SubList xs
  complement [] = []
  complement (x ∥ zs) = skip (complement zs)
  complement (skip {x} {xs} zs) = x ∥ complement zs

  -- Compute all sublists of a given list
  sublists : {A : Set}(xs : List A) -> List (SubList xs)
  sublists [] = [ [] ]
  sublists (x ∷ xs) with sublists xs 
  ... | ys = (map (_∥_ x) ys) ++ ((map skip ys))

  lst1 : List ℕ
  lst1 = 1 ∷ 2 ∷ 3 ∷ []

  subsLst1 : List (SubList lst1)
  subsLst1 = sublists lst1
