record 𝔐𝔬𝔫-Alg where
    (M : Set) 
    ((u : M)) 
    ((m : M → M → M)) 
    ((lunit : (x : M) → m (u) (x) = x)) 
    ((runit : (x : M) → m (x) (u) = x)) 
    ((assoc : (x : M) → (y : M) → (z : M) → m (x) (m (y) (z)) = m (m (x) (y)) (z)))