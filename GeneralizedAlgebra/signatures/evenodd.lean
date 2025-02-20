import GeneralizedAlgebra.nouGAT

def 𝔈𝔒_data := [namedGAT|
    Even  : U,
    Odd   : U,
    zero  : Even,
    succ  : Even ⇒ Odd,
    succ' : Odd ⇒ Even
]
def 𝔈𝔒 : GAT := 𝔈𝔒_data.1
def EvenOdd_names := 𝔈𝔒_data.2.1
def EvenOdd_topnames := 𝔈𝔒_data.2.2
