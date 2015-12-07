module Tests where

open import Data.List hiding ([_])
open import Data.Maybe
open import Data.Nat

open import SystemF

-- converts bindings list to context if possible
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

-- Tests --
x = v 0
y = v 1
z = v 2
a = v 3
b = v 4
X = tv 5
Y = tv 6
f = v 7

test1 = typecheck (x :- NAT ∷ []) (var x)

id = tlam X ▴ lam x :- (TVAR X) ▴ (var x)
test2 = typecheck [] id

idNat = lam x :- NAT ▴ (var x)
test3 = typecheck [] idNat
test4 = typecheck ((y :- NAT) ∷ []) idNat
test5 = typecheck ((y :- NAT) ∷ []) (idNat $ (var y))

test6 = typecheck ((y :- NAT) ∷ []) (id [ NAT ] $ (var y))

double = tlam X ▴ (lam f :- (TVAR X ⇒ TVAR X) ▴ (lam a :- TVAR X ▴ (var f $ (var f $ var a))))
testDouble = typecheck [] double
testDoubleNatArrowNat = typecheck [] (double [ NAT ⇒ NAT ])

A = ALL X ▴ TVAR X ⇒ TVAR X
testSelfApp = typecheck [] (lam x :- A ▴ (var x [ A ] $ var x))

tru = tlam X ▴ (lam x :- TVAR X ▴ (lam y :- TVAR X ▴ var x))
testTru = typecheck [] tru

CBool = ALL X ▴ TVAR X ⇒ TVAR X ⇒ TVAR X
not = lam b :- CBool ▴ (tlam X ▴ (lam x :- TVAR X ▴ (lam y :- TVAR X ▴ (var b [ TVAR X ] $ var y $ var x))))
testNot = typecheck [] not

R = tv 0
LIST : TVar → Type
LIST X = ALL R ▴ (TVAR X ⇒ TVAR R ⇒ TVAR R) ⇒ TVAR R ⇒ TVAR R
hd = v 1
tl = v 2
c = v 3
n = v 4
cons = tlam X ▴ (lam hd :- TVAR X ▴ (lam tl :- LIST X ▴ 
       (tlam R ▴ (lam c :- TVAR X ⇒ TVAR R ⇒ TVAR R ▴ (lam n :- TVAR R ▴ (var c $ var hd $ (var tl [ TVAR R ] $ var c $ var n)))))
       ))
testCons = typecheck [] cons
