record 𝔓𝔯𝔢𝔒𝔯𝔡-Alg where
    (X : Set) 
    ((leq : X → X → Set)) 
    ((leqη : (x : X) → (x' : X) → (p : leq (x) (x')) → (q : leq (x) (x')) → p = q)) 
    ((rfl : (x : X) → leq (x) (x))) 
    ((trns : (x : X) → (y : X) → (z : X) → leq (x) (y) → leq (y) (z) → leq (x) (z)))