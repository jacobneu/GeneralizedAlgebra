import GeneralizedAlgebra.nouGAT

def 𝔈𝔒_data : GATdata := [GATdata|
    Even  : U,
    Odd   : U,
    zero  : Even,
    succ  : Even ⇒ Odd,
    succ' : Odd ⇒ Even
]

def 𝔈𝔒 : GAT := ⟨
    𝔈𝔒_data,
    by
        apply wellCon.wellCons
        apply wellTy.wellPI
        repeat apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        apply wellTy.wellUU

        apply wellCon.wellCons
        apply wellTy.wellPI
        repeat apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        apply wellTy.wellUU

        apply wellCon.wellCons
        apply wellTy.wellEL
        apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        apply wellCon.wellCons
        apply wellTy.wellUU

        apply wellCon.wellCons
        apply wellTy.wellUU

        apply wellCon.wellEmpty
⟩
