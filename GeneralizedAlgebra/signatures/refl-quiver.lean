import GeneralizedAlgebra.signatures.quiver

def 𝔯𝔔𝔲𝔦𝔳 : GAT_sig :=
  include 𝔔𝔲𝔦𝔳 as (V,E);
    r : (v : V) ⇒ E v v
