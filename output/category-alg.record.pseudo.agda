record ℭ𝔞𝔱-Alg where
    (Obj : Set) 
    ((Hom : Obj → Obj → Set)) 
    ((id : (X : Obj) → Hom (X) (X))) 
    ((comp : (X : Obj) → (Y : Obj) → (Z : Obj) → Hom (Y) (Z) → Hom (X) (Y) → Hom (X) (Z))) 
    ((lunit : (X : Obj) → (Y : Obj) → (f : Hom (X) (Y)) → comp (X) (Y) (Y) (id (Y)) (f) = f)) 
    ((runit : (X : Obj) → (Y : Obj) → (f : Hom (X) (Y)) → comp (X) (X) (Y) (f) (id (X)) = f)) 
    ((assoc : (W : Obj) → (X : Obj) → (Y : Obj) → (Z : Obj) → (e : Hom (W) (X)) → (f : Hom (X) (Y)) → (g : Hom (Y) (Z)) → comp (W) (X) (Z) (g) (comp (W) (X) (Y) (f) (e)) = comp (W) (Y) (Z) (comp (X) (Y) (Z) (g) (f)) (e)))