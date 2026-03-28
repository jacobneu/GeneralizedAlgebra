import GeneralizedAlgebra.nouGAT_eliminate

def ℭ𝔞𝔱_data  := [GATdata|
    Obj : U,
    Hom : Obj ⇒ Obj ⇒ U,
    id  : (X : Obj) ⇒ Hom X X,
    comp  : (X :Obj) ⇒ (Y : Obj) ⇒ (Z : Obj) ⇒
             Hom Y Z ⇒ Hom X Y ⇒ Hom X Z,
    lunit : (X : Obj) ⇒ (Y : Obj) ⇒  (f : Hom X Y) ⇒
            comp X Y Y (id Y) f ≡ f,
    runit : (X : Obj) ⇒ (Y : Obj) ⇒ (f : Hom X Y) ⇒
            comp X X Y f (id X) ≡ f,
    assoc : (W:Obj) ⇒ (X:Obj) ⇒ (Y:Obj) ⇒ (Z:Obj) ⇒ (e : Hom W X) ⇒
            (f : Hom X Y) ⇒ (g : Hom Y Z) ⇒
            comp W Y Z g (comp W X Y f e) ≡ comp W X Z (comp X Y Z g f) e
]
def Cat_names_alt1 := ["Obj","Mor","I","id", "I", "J", "K","comp","I","J","j","idr","I","J","K","idl","I","J","K","L","j","k","l","ass"]
