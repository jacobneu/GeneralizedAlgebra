import GeneralizedAlgebra.nouGAT_eliminate

def 𝔈𝔒 : GAT := ⦃
    Even  : U,
    Odd   : U,
    zero  : Even,
    succ  : Even ⇒ Odd,
    succ' : Odd ⇒ Even
⦄
