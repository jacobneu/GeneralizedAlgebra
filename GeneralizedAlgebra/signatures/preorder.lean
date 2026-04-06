import GeneralizedAlgebra.nouGAT_eliminate

def 𝔓𝔯𝔢𝔒𝔯𝔡_data : GATdata := [GATdata|
    X : U,
    leq : X ⇒ X ⇒ U,
    leqη : (x x' : X) ⇒ (p q : leq x x') ⇒ p ≡ q,
    rfl : (x : X) ⇒ leq x x,
    trns : (x y z : X) ⇒ leq x y ⇒ leq y z ⇒ leq x z
]
