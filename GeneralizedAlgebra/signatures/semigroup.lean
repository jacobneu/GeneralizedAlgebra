import GeneralizedAlgebra.nouGAT_eliminate

def 𝔖𝔢𝔪𝔦𝔊𝔯𝔭 : GAT := ⦃
    M     : U,
    m     : M ⇒ M ⇒ M,
    assoc : (x y z : M) ⇒ m x (m y z) ≡ m (m x y) z
⦄
