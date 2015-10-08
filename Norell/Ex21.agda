module Ex21 where
  open import Data.Vec
  open import Data.Nat
  
  Matrix : Set → ℕ → ℕ → Set
  Matrix A n m = Vec (Vec A n) m

  vec : {n : ℕ} {A : Set} → A → Vec A n
  vec {zero} x = []
  vec {suc n} x = x ∷ (vec {n} x)

  infix 90 _$_
  _$_ : {n : ℕ} {A B : Set} → Vec (A → B) n → Vec A n → Vec B n
  fs $ [] = []
  (f ∷ fs) $ (x ∷ xs) = f x ∷ fs $ xs

  transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
  transpose [] = vec []
  transpose (ms ∷ mss) = (map _∷_ ms) $ (transpose mss)

  m : Matrix ℕ 3 2
  m = (1 ∷ 3 ∷ 4 ∷ []) ∷ (2 ∷ 4 ∷ 6 ∷ []) ∷ []

  mt : Matrix ℕ 2 3
  mt = transpose m
