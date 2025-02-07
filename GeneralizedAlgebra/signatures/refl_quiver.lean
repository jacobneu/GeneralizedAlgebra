import GeneralizedAlgebra.nouGAT

def 𝔯𝔔𝔲𝔦𝔳_data := [namedGAT|
    V : U,
    E : V ⇒ V ⇒ U,
    r : (v : V) ⇒ E v v
]
def 𝔯𝔔𝔲𝔦𝔳 : GAT := 𝔯𝔔𝔲𝔦𝔳_data.1
def rQuiv_names := 𝔯𝔔𝔲𝔦𝔳_data.2.1
def rQuiv_topnames := 𝔯𝔔𝔲𝔦𝔳_data.2.2
