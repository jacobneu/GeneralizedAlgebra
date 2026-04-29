import GeneralizedAlgebra.nouGAT_eliminate

def 𝔲𝔊𝔯𝔞𝔭𝔥 : GAT :=
⦃
    V : U,
    E : V ⇒ V ⇒ U,
    Eη : {v w : V} ⇒ (e e' : E v w) ⇒ e ≡ e',
    Esym : {v w : V} ⇒ E v w ⇒ E w v
⦄
