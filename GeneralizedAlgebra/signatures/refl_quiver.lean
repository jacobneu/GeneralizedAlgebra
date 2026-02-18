import GeneralizedAlgebra.signatures.quiver

def 𝔯𝔔𝔲𝔦𝔳_data : GATdata := [GATdata|
    V : U,
    E : V ⇒ V ⇒ U,
    r : (v : V) ⇒ E v v
]

def 𝔯𝔔𝔲𝔦𝔳 : GAT := ⟨
    𝔯𝔔𝔲𝔦𝔳_data,
    by
        apply wellCon.wellCons
        apply wellTy.wellPI

        -- V : U in context extended by E
        apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- El(E v v) is a type
        apply wellTy.wellEL

        -- E v v : U
        apply @wellTm.wellAPP _ (preTm.preVAR 2) preTy.preUU
        -- E v : V ⇒ U
        apply @wellTm.wellAPP _ (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) preTy.preUU)
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 1) (preTy.prePI (preTm.preVAR 2) preTy.preUU))
        apply wellTm.wellZero
        apply wellTy.wellPI
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellPI
        apply @wellTm.wellWkTm _ preTy.preUU;
        apply wellTm.wellZero
        repeat apply wellTy.wellUU

        repeat -- v : V
            apply wellTm.wellZero
            apply wellTy.wellEL
            apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU

        exact 𝔔𝔲𝔦𝔳.2
⟩
