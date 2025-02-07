import GeneralizedAlgebra.nouGAT

def 𝔓𝔯𝔢𝔒𝔯𝔡_data := [namedGAT|
    X : U,
    leq : X ⇒ X ⇒ U,
    leqη : (x : X) ⇒ (x' : X) ⇒
        (p : leq x x') ⇒ (q : leq x x') ⇒ p ≡ q,
    rfl : (x : X) ⇒ leq x x,
    trns : (x : X) ⇒ (y : X) ⇒ (z : X) ⇒
        leq x y ⇒ leq y z ⇒ leq x z
]
def 𝔓𝔯𝔢𝔒𝔯𝔡 : GAT := 𝔓𝔯𝔢𝔒𝔯𝔡_data.1
def PreOrd_names := 𝔓𝔯𝔢𝔒𝔯𝔡_data.2.1
def PreOrd_topnames := 𝔓𝔯𝔢𝔒𝔯𝔡_data.2.2
