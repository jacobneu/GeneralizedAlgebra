import GeneralizedAlgebra.nouGAT

def 𝔅_data := [namedGAT|
    X : U,
    x₀ : X,
    x₁ : X
]
def 𝔅 : GAT := 𝔅_data.1
def Bipointed_names := 𝔅_data.2.1
def Bipointed_topnames := 𝔅_data.2.2
