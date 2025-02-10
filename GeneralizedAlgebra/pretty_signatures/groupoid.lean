import GeneralizedAlgebra.pretty_signatures.category

def 𝔊𝔯𝔭𝔡 : GAT := ⦃
  include ℭ𝔞𝔱 as (Obj,Hom,comp,id);
    inv  :  {X Y : Obj} ⇒ Hom X Y ⇒ Hom Y X,
    linv :  {X Y : Obj} ⇒ (f : Hom X Y) ⇒
            comp (inv f) f ≡ id Y,
    rinv :  {X Y : Obj} ⇒ (f : Hom X Y) ⇒
            comp f (inv f) ≡ id X
⦄
