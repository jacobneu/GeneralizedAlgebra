import GeneralizedAlgebra.signatures.set

def 𝔔𝔲𝔦𝔳_data : GATdata := [GATdata|
    V : U,
    E : V ⇒ V ⇒ U
]

def 𝔔𝔲𝔦𝔳 : GAT := ⟨
    𝔔𝔲𝔦𝔳_data,
    by
        apply wellCon.wellCons
        apply wellTy.wellPI
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellPI

        apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        apply wellTy.wellUU

        apply wellTy.wellUU

        exact 𝔖𝔢𝔱.2
⟩
