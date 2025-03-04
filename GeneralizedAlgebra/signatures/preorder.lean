import GeneralizedAlgebra.nouGAT

def 𝔓𝔯𝔢𝔒𝔯𝔡 : GAT := ⦃
    X : U,
    leq : X ⇒ X ⇒ U,
    leqη : (x : X) ⇒ (x' : X) ⇒
        (p : leq x x') ⇒ (q : leq x x') ⇒ p ≡ q,
    rfl : (x : X) ⇒ leq x x,
    trns : (x : X) ⇒ (y : X) ⇒ (z : X) ⇒
        leq x y ⇒ leq y z ⇒ leq x z
⦄
