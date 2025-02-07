import GeneralizedAlgebra.nouGAT

def 𝔐𝔬𝔫_data := [namedGAT|
    M     : U,
    m     : M ⇒ M ⇒ M,
    u     : M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x : M) ⇒ (y : M) ⇒ (z : M) ⇒ m x (m y z) ≡ m (m x y) z
]
def 𝔐𝔬𝔫 : GAT := 𝔐𝔬𝔫_data.1
def Mon_names := 𝔐𝔬𝔫_data.2.1
def Mon_topnames := 𝔐𝔬𝔫_data.2.2
