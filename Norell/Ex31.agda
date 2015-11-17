module Ex31 where

open import Data.Nat

data Compare : ℕ → ℕ → Set where
  less : ∀ {n} k → Compare n (n + suc k)
  more : ∀ {n} k → Compare (n + suc k) n
  same : ∀ {n} → Compare n n

-- (a) Define the view function
compare' : (n m : ℕ) -> Compare n m
compare' zero zero = same
compare' zero (suc y) = less {zero} y
compare' (suc x) zero = more {zero} x
compare' (suc x) (suc y) with compare' x y
compare' (suc a) (suc .a) | same = same
compare' (suc a) (suc .(a + suc k)) | less {.a} k = less {suc a} k
compare' (suc .(b + suc k)) (suc b) | more {.b} k = more {suc b} k

-- (b) Now use the view to compute the difference between two numbers
difference : ℕ → ℕ → ℕ
difference n m with compare' n m
difference n .n | same = 0
difference n .(n + suc k) | less k = suc k
difference .(m + suc k) m | more k = suc k
