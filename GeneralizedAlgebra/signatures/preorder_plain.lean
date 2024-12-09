import GeneralizedAlgebra.signature_plain

def 𝔓𝔯𝔢𝔒𝔯𝔡 : GAT := ⦃
    X : U,
    leq : X ⇒ X ⇒ U,
    rfl : (x : X) ⇒ leq x x,
    leqη : (x : X) ⇒ (x' : X) ⇒
        (p : leq x x') ⇒ (q : leq x x') ⇒ p ≡ q,
    trns : (x : X) ⇒ (y : X) ⇒ (z : X) ⇒
        leq x y ⇒ leq y z ⇒ leq x z
⦄
#eval Con_toString 𝔓𝔯𝔢𝔒𝔯𝔡
