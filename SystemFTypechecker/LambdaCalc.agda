module LambdaCalc where

open import Data.Nat
open import Data.List

open import ListUtils

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type → Type → Type

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no : forall {σ τ} -> Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
ı =?= ı = yes
ı =?= (_ ⇒ _) = no
(_ ⇒ _) =?= ı = no
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ ⇒ τ) =?= (.σ ⇒ .τ) | yes | yes = yes
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) | _ | _ = no

infixl 80 _$_
data Raw : Set where
  var : ℕ -> Raw
  _$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (Γ : Cxt) : Type -> Set where
  var : forall {τ} -> τ ∈ Γ -> Term Γ τ
  _$_ : forall {σ τ} -> Term Γ (σ ⇒ τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ {τ} -> Term (σ ∷ Γ) τ -> Term Γ (σ ⇒ τ)

erase : forall {Γ τ} -> Term Γ τ -> Raw
erase (var x) = var (index x)
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data Infer (Γ : Cxt) : Raw -> Set where
  ok : (τ : Type)(t : Term Γ τ) -> Infer Γ (erase t)
  bad : {e : Raw} -> Infer Γ e

infer : (Γ : Cxt)(e : Raw) -> Infer Γ e

infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad
infer Γ (var .(index x)) | inside σ x = ok σ (var x)

infer Γ (e1 $ e2) with infer Γ e1
infer Γ (e1 $ e2) | bad = bad
infer Γ (.(erase t1) $ e2) | ok ı t1 = bad
infer Γ (.(erase t1) $ e2) | ok (σ ⇒ τ) t1 with infer Γ e2
infer Γ (.(erase t1) $ e2) | ok (σ ⇒ τ) t1 | bad = bad
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ’ t2 with σ =?= σ’
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok .σ t2 | yes = ok τ (t1 $ t2)
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ’ t2 | no = bad

infer Γ (lam σ e) with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ e) | bad = bad
