module Ex22 where
  open import Data.Fin using (Fin; suc; zero)
  open import Data.Nat
  open import Data.Vec

  _!_ : {n : ℕ} {A : Set} → Vec A n → Fin n → A
  [] ! ()
  (x ∷ xs) ! zero = x
  (x ∷ xs) ! (suc i) = xs ! i

--  tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
--  tabulate {zero} f = []
--  tabulate {suc n} f = f zero :: tabulate (f ◦ suc)

  data False : Set where
  record True : Set where

  data _==_ {A : Set}(x : A) : A → Set where
    refl : x == x

  lem-!-tab : ∀ {A n} (f : Fin n → A) (i : Fin n) → (tabulate f ! i) == (f i)
  lem-!-tab f zero = refl
  lem-!-tab f (suc i) = lem-!-tab (λ z → f (suc z)) i

  lem-tab-! : ∀ {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
  lem-tab-! [] = refl
  lem-tab-! (x ∷ xs) with tabulate (_!_ xs) | lem-tab-! xs 
  ... | .xs | refl = refl

  data _≠_ : ℕ → ℕ → Set where
    z≠s : {n : ℕ} → zero ≠ suc n
    s≠z : {n : ℕ} → suc n ≠ zero
    s≠t : {n m : ℕ} → n ≠ m → (suc n) ≠ (suc m)

  data Equal? (n m : ℕ) : Set where
    eq : n == m → Equal? n m
    neq : n ≠ m → Equal? n m

  equal? : (n m : ℕ) → Equal? n m
  equal? zero zero = eq refl
  equal? zero (suc m) = neq z≠s
  equal? (suc n) zero = neq s≠z
  equal? (suc n) (suc m) with equal? n m
  equal? (suc n) (suc .n) | eq refl = eq refl
  equal? (suc n) (suc m)  | neq p = neq (s≠t p)
  
  lem-plus-zero : (n : ℕ) → (n + zero) == n
  lem-plus-zero zero = refl
  lem-plus-zero (suc m) with m + zero | lem-plus-zero m
  ... | .m | refl = refl


  
