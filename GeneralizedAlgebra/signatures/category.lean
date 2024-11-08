import GeneralizedAlgebra.signature

def ℭ𝔞𝔱 : GAT_sig :=
    Obj   : U,
    Hom   : Obj ⇒ Obj ⇒ U,
    comp  : (X Y Z : U) ⇒
            Hom Y Z ⇒ Hom X Y ⇒ Hom X Z,
    id    : (X : Obj) ⇒ Hom X X,
    lunit : (X Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp (id Y) f ≡ f,
    runit : (X Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp f (id X) ≡ f,
    assoc : (W X Y Z : Obj) ⇒ (e : Hom W X) ⇒
            (f : Hom X Y) ⇒ (g : Hom Y Z) ⇒
            comp g (comp f e) ≡ comp (comp g f) e
