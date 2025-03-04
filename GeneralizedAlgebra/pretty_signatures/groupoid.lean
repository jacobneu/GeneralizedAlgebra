import GeneralizedAlgebra.pretty_signatures.category

def 𝔊𝔯𝔭𝔡 : GAT := ⦃
  include ℭ𝔞𝔱 as (Obj,Mor,id,comp);
    inv  :  {I J : Obj} ⇒ Mor I J ⇒ Mor J I,
    linv :  {I J : Obj} ⇒ (j : Mor I J) ⇒
            comp (inv j) j ≡ id I,
    rinv :  {I J : Obj} ⇒ (j : Mor I J) ⇒
            comp j (inv j) ≡ id J
⦄
