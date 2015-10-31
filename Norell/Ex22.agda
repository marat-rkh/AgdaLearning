module Ex22 where
  open import Data.Fin
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
  lem-tab-! (x ∷ xs) | .xs | refl = refl
