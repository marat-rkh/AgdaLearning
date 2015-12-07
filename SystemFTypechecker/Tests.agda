module Tests where

open import Data.List hiding ([_])
open import Data.Maybe
open import Data.String

open import SystemF

open import Data.Nat

ctxt? : (bs : List Binding) → Maybe (Ctxt bs)
ctxt? [] = just ∅
ctxt? (b ∷ bs) with ctxt? bs
ctxt? (b ∷ bs) | just Γ with isFresh b Γ
ctxt? (b ∷ bs) | just Γ | just fp = just (Γ , b [ fp ])
ctxt? (b ∷ bs) | just Γ | _ = nothing
ctxt? (b ∷ bs) | _ = nothing

getType : ∀ {t T bs} → {Γ : Ctxt bs} → (Γ ⊢ t :- T) → Type
getType {_} {T} {_} {_} _ = T

data TypecheckRes : Set where
  incorrectCtxt : TypecheckRes
  hasType_withDerivationTree_ : ∀ {t bs} → {Γ : Ctxt bs} → (T : Type) → (Γ ⊢ t :- T) → TypecheckRes
  cannotBeTyped : TypecheckRes

typecheck : (bs : List Binding) → (rt : RawTerm) → TypecheckRes
typecheck bs rt with ctxt? bs
typecheck bs rt | just Γ with infer Γ rt
typecheck bs rt | just Γ | typed prf = hasType (getType prf) withDerivationTree prf
typecheck bs rt | just Γ | bad = cannotBeTyped
typecheck bs rt | nothing = incorrectCtxt

x = v 0
y = v 1
z = v 2
a = v 3
b = v 4
X = tv 5
Y = tv 6
idNat = lam x :- NAT ▴ (var x)
id = tlam X ▴ lam x :- (TVAR X) ▴ (var x)

test1 = typecheck (x :- NAT ∷ []) (var x)

test2 = typecheck [] id

test3 = typecheck [] idNat

test4 = typecheck ((y :- NAT) ∷ []) idNat

test5 = typecheck ((y :- NAT) ∷ []) (idNat $ (var y))

test6 = typecheck ((y :- NAT) ∷ []) (id [ NAT ] $ (var y))

testSelfApp = typecheck [] (lam x :- A ▴ (var x [ A ] $ var x))
  where A = ALL X ▴ TVAR X ⇒ TVAR X
