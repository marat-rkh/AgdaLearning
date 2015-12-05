module SystemF where

open import Data.Nat
open import Data.List

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type → Type → Type

data Var : Set where
  var : ℕ → Var

data TVar : Set where
  tvar : ℕ → TVar

infix 50 _:ₜ_
data Binding : Set where
  _:ₜ_ : Var → Type → Binding
  tb : TVar → Binding

freshVar : List Binding → Var
freshVar [] = var 0
freshVar ((var n :ₜ _) ∷ bs) = var (suc n)
freshVar (_ ∷ bs) = freshVar bs

freshTVar : List Binding → TVar
freshTVar [] = tvar 0
freshTVar (tb (tvar n) ∷ bs) = tvar (suc n)
freshTVar (_ ∷ bs) = freshTVar bs

infixr 30 _+vb_
infixr 30 _+tb_
data Ctxt : (bindings : List Binding) → Set where
  ∅ : Ctxt []
  _+vb_ : ∀ {bs} → (t : Type) → (c : Ctxt bs) → Ctxt (freshVar bs :ₜ t ∷ bs)
  _+tb_ : ∀ {bs} → (c : Ctxt bs) → Ctxt (tb (freshTVar bs) ∷ bs)
