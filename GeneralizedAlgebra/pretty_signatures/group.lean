import GeneralizedAlgebra.nouGAT

def 𝔊𝔯𝔭 : GAT := ⦃
    include 𝔐𝔬𝔫 as (M,u,m);
    inv   : M ⇒ M,
    linv  : (x : M) ⇒ m (inv x) x ≡ u,
    rinv  : (x : M) ⇒ m x (inv x) ≡ u
⦄
