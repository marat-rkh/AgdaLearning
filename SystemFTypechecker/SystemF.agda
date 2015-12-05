module SystemF where

open import Data.Nat
open import Data.List

-- variable with number as name
data Var : Set where
  v : ℕ → Var

-- type variable with number as name
data TVar : Set where
  tv : ℕ → TVar

-- type construction rules
infixr 30 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type
  tvar : TVar → Type
  all_∷_ : TVar → Type → Type

-- term construction rules
data RawTerm : Set where
  var : Var → RawTerm
  lam_∷_⇒_ : Var → Type → RawTerm → RawTerm
  _$_ : RawTerm → RawTerm → RawTerm
  tlam_∷_ : TVar → RawTerm → RawTerm
  _[_] : RawTerm → Type → RawTerm

-- context construction utils
-- data VarBinding : Set where
--   _:ₜ_ : Var → Type → VarBinding

infix 50 _:ₜ_
data Binding : Set where
  _:ₜ_ : Var → Type → Binding
  tb : TVar → Binding

freshVar : List Binding → Var
freshVar [] = v 0
freshVar ((v n :ₜ _) ∷ bs) = v (suc n)
freshVar (_ ∷ bs) = freshVar bs

freshTVar : List Binding → TVar
freshTVar [] = tv 0
freshTVar (tb (tv n) ∷ bs) = tv (suc n)
freshTVar (_ ∷ bs) = freshTVar bs

-- context construction rules
infixr 30 _+vb_
infixr 30 _+tb_
data Ctxt : List Binding → Set where
  ∅ : Ctxt []
  _+vb_ : ∀ {bs} → (t : Type) → (c : Ctxt bs) → Ctxt ((freshVar bs :ₜ t) ∷ bs)
  _+tb_ : ∀ {bs} → (c : Ctxt bs) → Ctxt (tb (freshTVar bs) ∷ bs)

-- typing rules utils
open import ListUtils

-- represents typing rules
data _⊢_:ₜ_ {bs : List Binding} (Γ : Ctxt bs) : RawTerm → Type → Set where
  var : ∀ {v τ} → (v :ₜ τ) ∈ bs → Γ ⊢ var v :ₜ τ
--  _$_ : forall {σ τ} -> Term Γ (σ ⇒ τ) -> Term Γ σ -> Term Γ τ
--  lam : forall σ {τ} -> Term (σ ∷ Γ) τ -> Term Γ (σ ⇒ τ)

