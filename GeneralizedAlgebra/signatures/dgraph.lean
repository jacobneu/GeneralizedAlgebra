import GeneralizedAlgebra.nouGAT_eliminate

def 𝔡𝔊𝔯𝔞𝔭𝔥 : GAT :=
⦃
    V : U,
    E : V ⇒ V ⇒ U,
    Eη : (v w : V) ⇒ (e e' : E v w) ⇒ e ≡ e'
⦄
