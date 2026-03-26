import GeneralizedAlgebra.nouGAT

def 𝔊𝔯𝔭𝔡_data : GATdata := [GATdata|
    Obj : U,
    Hom : Obj ⇒ Obj ⇒ U,
    id  : (X : Obj) ⇒ Hom X X,
    comp  : (X :Obj) ⇒ (Y : Obj) ⇒ (Z : Obj) ⇒
            Hom Y Z ⇒ Hom X Y ⇒ Hom X Z,
    lunit : (X : Obj) ⇒ (Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp X Y Y (id Y) f ≡ f,
    runit : (X : Obj) ⇒ (Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp X X Y f (id X) ≡ f,
    assoc : (W:Obj) ⇒ (X:Obj) ⇒ (Y:Obj) ⇒ (Z:Obj) ⇒ (e : Hom W X) ⇒
            (f : Hom X Y) ⇒ (g : Hom Y Z) ⇒
            comp W Y Z g (comp W X Y f e) ≡ comp W X Z (comp X Y Z g f) e,
    inv : (X:Obj) ⇒ (Y:Obj) ⇒ Hom X Y ⇒ Hom Y X,
    linv :  (X : Obj) ⇒ (Y : Obj) ⇒ (f : Hom X Y) ⇒
        comp X Y X (inv X Y f) f ≡ id X,
    rinv :  (X : Obj) ⇒ (Y : Obj) ⇒ (f : Hom X Y) ⇒
        comp Y X Y f (inv X Y f) ≡ id Y
]
