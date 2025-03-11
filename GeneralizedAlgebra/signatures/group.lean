import GeneralizedAlgebra.nouGAT

def 𝔊𝔯𝔭 : GAT := ⦃
    M     : U,
    u     : M,
    m     : M ⇒ M ⇒ M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x : M) ⇒ (y : M) ⇒ (z : M) ⇒ m x (m y z) ≡ m (m x y) z,
    inv   : M ⇒ M,
    linv  : (x : M) ⇒ m (inv x) x ≡ u,
    rinv  : (x : M) ⇒ m x (inv x) ≡ u
⦄
