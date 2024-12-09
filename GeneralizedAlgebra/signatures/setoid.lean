import GeneralizedAlgebra.signatures.preorder

def 𝔖𝔢𝔱𝔬𝔦𝔡 : GAT := ⦃
    include 𝔓𝔯𝔢𝔒𝔯𝔡 as (X,eq,_,_,_);
    sym : (x : X) ⇒ (y : X) ⇒ eq x y ⇒ eq y x
⦄
