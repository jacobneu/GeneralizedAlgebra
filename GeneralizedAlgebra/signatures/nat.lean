import GeneralizedAlgebra.signatures.pointed

def 𝔑_data : GATdata := [GATdata|
    N  : U,
    z  : N,
    s  : N ⇒ N
]

-- def 𝔑 : GAT := ⟨
--     𝔑_data,
--     by
--         apply wellCon.wellCons
--         apply wellTy.wellPI
--         apply @wellTm.wellWkTm _ preTy.preUU
--         apply wellTm.wellZero
--         apply wellTy.wellUU
--         apply wellTy.wellEL
--         apply @wellTm.wellWkTm _ preTy.preUU
--         apply @wellTm.wellWkTm _ preTy.preUU
--         apply wellTm.wellZero
--         apply wellTy.wellUU
--         exact 𝔓.2
-- ⟩
