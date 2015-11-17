module Ex32 where

open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; _∷_; length)
open import Ch3
open import Logic
open import Relation.Binary.PropositionalEquality
open import Data.Unit

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type → Type → Type

IsSimpleType : Type → Set
IsSimpleType ı = True
IsSimpleType _ = False

IsArrowType : Type → Set
IsArrowType (_ ⇒ _) = True
IsArrowType _ = False

data _≠_ : Type → Type → Set where
  ı≠⇒ : ∀ {τ σ} → IsSimpleType τ → IsArrowType σ → τ ≠ σ
  ⇒≠ı : ∀ {τ σ} → IsArrowType τ → IsSimpleType σ → τ ≠ σ
  dom-⇒≠⇒ : ∀ {τ σ α β} → τ ≠ σ → τ ⇒ α ≠ σ ⇒ β
  codom-⇒≠⇒ : ∀ {τ σ α β} → τ ≠ σ → α ⇒ τ ≠ β ⇒ σ

data Equal? : Type → Type → Set where
  yes : ∀ {τ} → Equal? τ τ
  no : ∀ {σ τ} → σ ≠ τ → Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
ı =?= ı = yes
ı =?= (_ ⇒ _) = no (ı≠⇒ _ _)
(_ ⇒ _) =?= ı = no (⇒≠ı _ _)
(σ1 ⇒ τ1) =?= (σ2 ⇒ τ2) with σ1 =?= σ2 | τ1 =?= τ2
(σ ⇒ τ) =?= (.σ ⇒ .τ) | yes | yes = yes
...                   | no prf | _ = no (dom-⇒≠⇒ prf)
...                   | _ | no prf = no (codom-⇒≠⇒ prf)

infixl 80 _$_
data Raw : Set where
  var : ℕ -> Raw
  _$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (Γ : Cxt) : Type -> Set where
  var : ∀ {τ} -> τ ∈ Γ -> Term Γ τ
  _$_ : ∀ {σ τ} -> Term Γ (σ ⇒ τ) -> Term Γ σ -> Term Γ τ
  lam : ∀ σ {τ} -> Term (σ ∷ Γ) τ -> Term Γ (σ ⇒ τ)

erase : ∀ {Γ τ} -> Term Γ τ -> Raw
erase (var x) = var (index x)
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data BadTerm (Γ : Cxt) : Set where
  var : (n : ℕ) → BadTerm Γ
  lam : ∀ σ → BadTerm (σ ∷ Γ) → BadTerm Γ
  bad$bad : BadTerm Γ → BadTerm Γ → BadTerm Γ
  bad$ok : ∀ {σ} → BadTerm Γ → Term Γ σ → BadTerm Γ
  ok$bad : ∀ {σ} → Term Γ σ → BadTerm Γ → BadTerm Γ
  ı$any : ∀ {σ} → Term Γ ı → Term Γ σ → BadTerm Γ
  ok$ok : ∀ {σ τ β} → Term Γ (σ ⇒ τ) → Term Γ β → σ ≠ β → BadTerm Γ

eraseBad : {Γ : Cxt} -> BadTerm Γ -> Raw
eraseBad {Γ} (var n) = var (length Γ + n)
eraseBad (lam σ t) = lam σ (eraseBad t)
eraseBad (bad$bad b₁ b₂) = (eraseBad b₁) $ (eraseBad b₂)
eraseBad (bad$ok b₁ b₂) = (eraseBad b₁) $ (erase b₂)
eraseBad (ok$bad b₁ b₂) = (erase b₁) $ (eraseBad b₂)
eraseBad (ı$any b₁ b₂) = (erase b₁) $ (erase b₂)
eraseBad (ok$ok b₁ b₂ _) = (erase b₁) $ (erase b₂)

data TypeInfo (Γ : Cxt) : Raw -> Set where
  typed : (τ : Type)(t : Term Γ τ) -> TypeInfo Γ (erase t)
  untypable : (b : BadTerm Γ) -> TypeInfo Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) -> TypeInfo Γ e

infer Γ (var n)                 with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = untypable (var n)
infer Γ (var .(index x))      | inside σ x = typed σ (var x)

infer Γ (e1 $ e2)                            with infer Γ e1 | infer Γ e2
infer Γ (.(eraseBad t1) $ .(eraseBad t2)) | untypable t1     | untypable t2 = untypable (bad$bad t1 t2)
infer Γ (.(erase t1) $ .(eraseBad t2))    | typed _ t1       | untypable t2 = untypable (ok$bad t1 t2)
infer Γ (.(eraseBad t1) $ .(erase t2))    | untypable t1     | typed _ t2 = untypable (bad$ok t1 t2)
infer Γ (.(erase t1) $ .(erase t2))       | typed ı t1       | typed _ t2 = untypable (ı$any t1 t2)
infer Γ (.(erase t1) $ .(erase t2))       | typed (σ ⇒ τ) t1 | typed β t2 with σ =?= β
infer Γ (.(erase t1) $ .(erase t2))       | typed (α ⇒ τ) t1 | typed .α t2 | yes = typed τ (t1 $ t2)
infer Γ (.(erase t1) $ .(erase t2))       | typed (σ ⇒ τ) t1 | typed β t2  | no prf = untypable (ok$ok t1 t2 prf)

infer Γ (lam σ e)          with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t))    | typed τ t = typed (σ ⇒ τ) (lam σ t)
infer Γ (lam σ .(eraseBad t)) | untypable t = untypable (lam σ t)
