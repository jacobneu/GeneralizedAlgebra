import GeneralizedAlgebra.signature

def 𝔐𝔬𝔫 : GAT_sig :=
    M     : U,
    m     : M ⇒ M ⇒ M,
    u     : M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x y z : M) ⇒ m x (m y z) ≡ m (m x y) z
