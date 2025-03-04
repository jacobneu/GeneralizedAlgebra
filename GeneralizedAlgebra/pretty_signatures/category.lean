import GeneralizedAlgebra.pretty_signatures.refl_quiver

def ℭ𝔞𝔱 : GAT := ⦃
  include 𝔯𝔔𝔲𝔦𝔳 as (Obj,Mor,id);
    comp  : {I J K : Obj} ⇒
            Mor J K ⇒ Mor I J ⇒ Mor I K,
    lunit : {I J : Obj} ⇒ (j : Mor I J) ⇒
            comp (id J) j ≡ j,
    runit : {I J : Obj} ⇒ (j : Mor I J) ⇒
            comp j (id I) ≡ j,
    assoc : {I J K L : Obj} ⇒ (j : Mor I J) ⇒
            (k : Mor J K) ⇒ ( ℓ : Mor K L) ⇒
            comp ℓ (comp k j) ≡ comp (comp ℓ k) j
⦄
