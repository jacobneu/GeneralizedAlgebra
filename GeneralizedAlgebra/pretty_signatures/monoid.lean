import GeneralizedAlgebra.nouGAT

def 𝔐𝔬𝔫 : GAT := ⦃
    M     : U,
    m     : M ⇒ M ⇒ M,
    u     : M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x : M) ⇒ (y : M) ⇒ (z : M) ⇒ m x (m y z) ≡ m (m x y) z
⦄
