import GeneralizedAlgebra.signatures.refl_quiver

def 𝔓𝔯𝔢𝔒𝔯𝔡 : GAT := ⦃
    include 𝔯𝔔𝔲𝔦𝔳 as (X,leq,_);
    leqη : (x : X) ⇒ (x' : X) ⇒
        (p : leq x x') ⇒ (q : leq x x') ⇒ p ≡ q,
    trns : (x : X) ⇒ (y : X) ⇒ (z : X) ⇒
        leq x y ⇒ leq y z ⇒ leq x z
⦄
