import GeneralizedAlgebra.pretty_signatures.preorder

def 𝔖𝔢𝔱𝔬𝔦𝔡 : GAT := ⦃
    include 𝔓𝔯𝔢𝔒𝔯𝔡 as (X,eq);
    sym : {x y : X} ⇒ eq x y ⇒ eq y x
⦄
