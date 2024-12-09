import GeneralizedAlgebra.signatures.refl_quiver

def ℭ𝔞𝔱 : GAT := ⦃
  include 𝔯𝔔𝔲𝔦𝔳 as (Obj,Hom,id);
    comp  : (X Y Z : U) ⇒
            Hom Y Z ⇒ Hom X Y ⇒ Hom X Z,
    lunit : (X Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp (id Y) f ≡ f,
    runit : (X Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp f (id X) ≡ f,
    assoc : (W X Y Z : Obj) ⇒ (e : Hom W X) ⇒
            (f : Hom X Y) ⇒ (g : Hom Y Z) ⇒
            comp g (comp f e) ≡ comp (comp g f) e
⦄
