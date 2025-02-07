import GeneralizedAlgebra.nouGAT

def 𝔑_data := [namedGAT|
    Nat   : U,
    zero  : Nat,
    suc   : Nat ⇒ Nat
]
def 𝔑 : GAT := 𝔑_data.1
def Nat_names := 𝔑_data.2.1
def Nat_topnames := 𝔑_data.2.2
