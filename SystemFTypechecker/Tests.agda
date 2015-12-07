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

typecheck : (bs : List Binding) → (rt : RawTerm) → String
typecheck bs rt with ctxt? bs
typecheck bs rt | just Γ with infer Γ rt
typecheck bs rt | just Γ | bad = "cannot be typed"
typecheck bs rt | just Γ | typed p = "type safe"
typecheck bs rt | nothing = "incorrect context"

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

testSelfApp = typecheck [] (lam x :- (ALL X ▴ TVAR X ⇒ TVAR X) ▴ ((var x [ ALL X ▴ TVAR X ⇒ TVAR X ]) $ var x))

-- test7 = typecheck (x :- (ALL X ▴ TVAR X ⇒ TVAR X) ∷ []) (var x [ ALL X ▴ TVAR X ⇒ TVAR X ] $ var x)

-- test8 = typecheck [] (lam x :- (ALL X ▴ TVAR X ⇒ TVAR X) ▴ var x [ ALL X ▴ TVAR X ⇒ TVAR X ])
