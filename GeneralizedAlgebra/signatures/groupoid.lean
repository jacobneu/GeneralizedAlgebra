import GeneralizedAlgebra.signature

def 𝔊𝔯𝔭𝔡 : GAT_sig :=
  include ℭ𝔞𝔱 as (Obj,Hom,comp,id,_,_,_);
    inv  :  (X Y : Obj) ⇒ Hom X Y ⇒ Hom Y X,
    linv :  (X Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp (inv f) f ≡ id Y,
    rinv :  (X Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp f (inv f) ≡ id X
