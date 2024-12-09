import GeneralizedAlgebra.signature_plain

def 𝔖𝔢𝔱𝔬𝔦𝔡 : GAT := ⦃
    X : U,
    eq : X ⇒ X ⇒ U,
    eqη : (x : X) ⇒ (x' : X) ⇒
        (p : eq x x') ⇒ (q : eq x x') ⇒ p ≡ q,
    rfl : (x : X) ⇒ eq x x,
    trns : (x : X) ⇒ (y : X) ⇒ (z : X) ⇒
        eq x y ⇒ eq y z ⇒ eq x z,
    sym : (x : X) ⇒ (y : X) ⇒
        eq x y ⇒ eq y x
⦄
#eval Con_toString 𝔖𝔢𝔱𝔬𝔦𝔡
