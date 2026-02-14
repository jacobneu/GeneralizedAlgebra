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
-- ,
-- λ P => P.cons_D _ (𝔖𝔢𝔱.elim P) _ (P.PI_D _ _ _ (P.VAR0_D _ _ _ _ _) _ (P.PI_D _ _ _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) _ (P.VAR0_D _ _ _ _ _) _ _ _) _ (P.UU_D _ _)))
-- ⟩
