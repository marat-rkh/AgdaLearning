module SystemF where

open import Data.Nat
open import Data.List hiding (all ; [_])

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
  all_▴_ : TVar → Type → Type

-- term construction rules
data RawTerm : Set where
  var : Var → RawTerm
  lam_:-_▴_ : Var → Type → RawTerm → RawTerm
  _$_ : RawTerm → RawTerm → RawTerm
  tlam_▴_ : TVar → RawTerm → RawTerm
  _[_] : RawTerm → Type → RawTerm

-- context construction utils
-- data VarBinding : Set where
--   _:ₜ_ : Var → Type → VarBinding

infix 50 _:-_
data Binding : Set where
  _:-_ : Var → Type → Binding
  tb : TVar → Binding

freshVar : List Binding → Var
freshVar [] = v 0
freshVar ((v n :- _) ∷ bs) = v (suc n)
freshVar (_ ∷ bs) = freshVar bs

freshTVar : List Binding → TVar
freshTVar [] = tv 0
freshTVar (tb (tv n) ∷ bs) = tv (suc n)
freshTVar (_ ∷ bs) = freshTVar bs

-- context construction rules
infixr 30 _,_
infixr 30 _,X
data Ctxt : List Binding → Set where
  ∅ : Ctxt []
  _,_ : ∀ {bs} → (c : Ctxt bs) → (t : Type) → Ctxt ((freshVar bs :- t) ∷ bs)
  _,X : ∀ {bs} → (c : Ctxt bs) → Ctxt (tb (freshTVar bs) ∷ bs)

-- typing rules utils
open import ListUtils

lastVar : ∀ {vv T bs} → Ctxt (vv :- T ∷ bs) → Var
lastVar {vv} {T} {bs} cxtx = vv

lastTVar : ∀ {tt bs} → Ctxt (tb tt ∷ bs) → TVar
lastTVar {tt} {bs} cxtx = tt

-- substitution in type
infix 50 [_↦_]_
[_↦_]_ : TVar → Type → Type → Type
[ x ↦ s ] nat = nat
[ x ↦ s ] (t₁ ⇒ t₂) = [ x ↦ s ] t₁ ⇒ [ x ↦ s ] t₂
[ (tv n) ↦ s ] tvar (tv m) with compare n m
[ (tv .n) ↦ s ] tvar (tv .n) | equal n = s
[ (tv n) ↦ s ] tvar (tv m) | _ = tvar (tv m)
[ x ↦ s ] (all y ▴ t) = all y ▴ [ x ↦ s ] t 

-- represents typing rules
data _⊢_:-_ {bs : List Binding} (Γ : Ctxt bs) : RawTerm → Type → Set where
  T-Var : ∀ {v T} → (v :- T) ∈ bs → 
          Γ ⊢ var v :- T
  T-Abs : ∀ {t₂ T₁ T₂} → Γ , T₁ ⊢ t₂ :- T₂ → 
          Γ ⊢ lam (lastVar (Γ , T₁)) :- T₁ ▴ t₂ :- T₁ ⇒ T₂
  T-App : ∀ {t₁ t₂ T₁ T₂} → Γ ⊢ t₁ :- T₁ ⇒ T₂ → Γ ⊢ t₂ :- T₁ → 
          Γ ⊢ (t₁ $ t₂) :- T₂
  T-TAbs : ∀ {t₁ T₁} → Γ ,X ⊢ t₁ :- T₁ → 
           Γ ⊢ tlam (lastTVar (Γ ,X)) ▴ t₁ :- (all (lastTVar (Γ ,X)) ▴ T₁)
  T-TApp : ∀ {t X T S} → Γ ⊢ t :- (all X ▴ T) → 
           Γ ⊢ t [ S ] :- [ X ↦ S ] T
