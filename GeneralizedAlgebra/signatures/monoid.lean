import GeneralizedAlgebra.nouGAT_eliminate

def 𝔐𝔬𝔫 : GAT := ⦃
    M     : U,
    u     : M,
    m     : M ⇒ M ⇒ M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x y z : M) ⇒ m x (m y z) ≡ m (m x y) z
⦄
