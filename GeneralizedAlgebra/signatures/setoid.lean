import GeneralizedAlgebra.nouGAT_eliminate

def 𝔖𝔢𝔱𝔬𝔦𝔡_data : GATdata := [GATdata|
    X : U,
    eq : X ⇒ X ⇒ U,
    eqη : (x x' : X) ⇒ (p q : eq x x') ⇒ p ≡ q,
    rfl : (x : X) ⇒ eq x x,
    sym : (x y : X) ⇒ eq x y ⇒ eq y x,
    trns : (x y z : X) ⇒ eq x y ⇒ eq y z ⇒ eq x z
]
