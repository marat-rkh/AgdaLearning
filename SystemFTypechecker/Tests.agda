module Tests where

open import Data.List
open import Data.Maybe
open import Data.String

open import SystemF2

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
typecheck bs rt | just Γ | bad = "can not be typed"
typecheck bs rt | just Γ | typed p = "type safe"
typecheck bs rt | nothing = "incorrect context"

test1 : String
test1 = typecheck (v 0 :- NAT ∷ []) (var (v 0))

test2 : String
test2 = typecheck (tb X ∷ (x :- TVAR X) ∷ []) id
  where
    X = tv 2
    x = v 0   
    id = tlam X ▴ lam x :- (TVAR X) ▴ (var x)

test3 : String
test3 = typecheck [] id
  where
    x = v 0    
    id = lam x :- NAT ▴ (var x)

test4 : String
test4 = typecheck ((y :- NAT) ∷ []) id
  where
    x = v 2    
    y = v 0
    id = lam x :- NAT ▴ (var x)
