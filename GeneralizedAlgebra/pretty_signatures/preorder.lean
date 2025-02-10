import GeneralizedAlgebra.pretty_signatures.refl_quiver

def 𝔓𝔯𝔢𝔒𝔯𝔡 : GAT := ⦃
    include 𝔯𝔔𝔲𝔦𝔳 as (X,leq,_);
    leqη : {x x' : X} ⇒ {p q : leq x x'} ⇒ p ≡ q,
    trns : {x y z : X} ⇒ leq x y ⇒ leq y z ⇒ leq x z
⦄
