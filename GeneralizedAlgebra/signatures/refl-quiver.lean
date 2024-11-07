import GeneralizedAlgebra.signature

def 𝔯𝔔 : GAT_sig :=
    V : U,
    E : V ⇒ V ⇒ U,
    r : (v : V) ⇒ E v v
