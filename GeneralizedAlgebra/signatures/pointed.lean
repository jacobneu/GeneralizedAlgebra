import GeneralizedAlgebra.nouGAT

def 𝔓_data := [namedGAT|
    X : U,
    x : X
]
def 𝔓 : GAT := 𝔓_data.1
def Pointed_names := 𝔓_data.2.1
def Pointed_topnames := 𝔓_data.2.2
