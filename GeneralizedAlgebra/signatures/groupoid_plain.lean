import GeneralizedAlgebra.signature_plain

def 𝔊𝔯𝔭𝔡 := ⦃
    Obj : U,
    Mor : Obj ⇒ Obj ⇒ U,
    id  : (X : Obj) ⇒ Mor X X,
    comp  : (X :Obj) ⇒ (Y : Obj) ⇒ (Z : Obj) ⇒
            Mor Y Z ⇒ Mor X Y ⇒ Mor X Z,
    lunit : (X : Obj) ⇒ (Y : Obj) ⇒ (f : Mor X Y) ⇒
            comp X Y Y (id Y) f ≡ f,
    runit : (X : Obj) ⇒ (Y : Obj) ⇒ (f : Mor X Y) ⇒
            comp X X Y f (id X) ≡ f,
    assoc : (W:Obj) ⇒ (X:Obj) ⇒ (Y:Obj) ⇒ (Z:Obj) ⇒
        (e :Mor W X) ⇒ (f :Mor X Y) ⇒ (g :Mor Y Z) ⇒
        comp W X Z g (comp W X Y f e)
        ≡ comp W Y Z (comp X Y Z g f) e,
    inv : (X:Obj) ⇒ (Y:Obj) ⇒ Mor X Y ⇒ Mor Y X,
    linv :  (X : Obj) ⇒ (Y : Obj) ⇒ (f : Mor X Y) ⇒
        comp (inv f) f ≡ id Y,
    rinv :  (X : Obj) ⇒ (Y : Obj) ⇒ (f : Mor X Y) ⇒
        comp f (inv f) ≡ id X
⦄
