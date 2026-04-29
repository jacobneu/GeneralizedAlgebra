import GeneralizedAlgebra.nouGAT_eliminate

def 𝔊𝔯𝔭𝔡 : GAT := ⦃
    Obj : U,
    Hom : Obj ⇒ Obj ⇒ U,
    id  : (X : Obj) ⇒ Hom X X,
    comp  : {X Y Z : Obj} ⇒
             Hom Y Z ⇒ Hom X Y ⇒ Hom X Z,
    lunit : {X Y : Obj} ⇒  (f : Hom X Y) ⇒
            comp {X} {Y} {Y} (id Y) f ≡ f,
    runit : {X Y : Obj} ⇒ (f : Hom X Y) ⇒
            comp {X} {X} {Y} f (id X) ≡ f,
    assoc : {W X Y Z : Obj} ⇒ (e : Hom W X) ⇒ (f : Hom X Y) ⇒ (g : Hom Y Z) ⇒
            comp {W} {Y} {Z} g (comp {W} {X} {Y} f e) ≡ comp {W} {X} {Z} (comp {X} {Y} {Z} g f) e,
    inv : {X Y : Obj} ⇒ Hom X Y ⇒ Hom Y X,
    linv :  {X Y : Obj} ⇒ (f : Hom X Y) ⇒
        comp {X} {Y} {X} (inv {X} {Y} f) f ≡ id X,
    rinv :  {X Y : Obj} ⇒ (f : Hom X Y) ⇒
        comp {Y} {X} {Y} f (inv {X} {Y} f) ≡ id Y
⦄
