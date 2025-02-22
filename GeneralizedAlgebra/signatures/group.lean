import GeneralizedAlgebra.nouGAT

def 𝔊𝔯𝔭_data := [namedGAT|
    M     : U,
    m     : M ⇒ M ⇒ M,
    u     : M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x : M) ⇒ (y : M) ⇒ (z : M) ⇒ m x (m y z) ≡ m (m x y) z,
    inv   : M ⇒ M,
    linv  : (x : M) ⇒ m (inv x) x ≡ u,
    rinv  : (x : M) ⇒ m x (inv x) ≡ u
]
def 𝔊𝔯𝔭 : GAT := 𝔊𝔯𝔭_data.1
def Group_names := 𝔊𝔯𝔭_data.2.1
def Group_topnames := 𝔊𝔯𝔭_data.2.2
