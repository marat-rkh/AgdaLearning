module SystemF where

open import Data.Nat
open import Data.List

data TVar : Set where
  tvar : ℕ → TVar

data Var : Set where
  var : ℕ → Var

infixr 30 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type
  tvar : TVar → Type
  all_∷_ : TVar → Type → Type

data VarBinding : Set where
  _:ₜ_ : Var → Type → VarBinding

infix 50 _:ₜ_
data Binding : Set where
  vb : VarBinding → Binding
  tb : TVar → Binding

freshVar : List Binding → Var
freshVar [] = var 0
freshVar (vb (var n :ₜ _) ∷ bs) = var (suc n)
freshVar (_ ∷ bs) = freshVar bs

freshTVar : List Binding → TVar
freshTVar [] = tvar 0
freshTVar (tb (tvar n) ∷ bs) = tvar (suc n)
freshTVar (_ ∷ bs) = freshTVar bs

infixr 30 _+vb_
infixr 30 _+tb_
data Ctxt : List Binding → Set where
  ∅ : Ctxt []
  _+vb_ : ∀ {bs} → (t : Type) → (c : Ctxt bs) → Ctxt (vb (freshVar bs :ₜ t) ∷ bs)
  _+tb_ : ∀ {bs} → (c : Ctxt bs) → Ctxt (tb (freshTVar bs) ∷ bs)

data RawTerm : Set where
  var : Var -> RawTerm
  lam_∷_ : Type -> RawTerm -> RawTerm
  _$_ : RawTerm -> RawTerm -> RawTerm
  tlam_∷_ : VarBinding → RawTerm -> RawTerm

