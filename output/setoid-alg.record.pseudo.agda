record 𝔖𝔢𝔱𝔬𝔦𝔡-Alg where
    (X : Set) 
    ((eq : X → X → Set)) 
    ((eqη : (x : X) → (x' : X) → (p : eq (x) (x')) → (q : eq (x) (x')) → p = q)) 
    ((rfl : (x : X) → eq (x) (x))) 
    ((sym : (x : X) → (y : X) → eq (x) (y) → eq (y) (x))) 
    ((trns : (x : X) → (y : X) → (z : X) → eq (x) (y) → eq (y) (z) → eq (x) (z)))