import GeneralizedAlgebra.signatures.pointed

def 𝔑_data : GATdata := [GATdata|
    Nat   : U,
    zero  : Nat,
    succ  : Nat ⇒ Nat
]

def 𝔑 : GAT := ⟨
    𝔑_data,
    by
        apply wellCon.wellCons
        apply wellTy.wellPI
        apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellEL
        apply @wellTm.wellWkTm _ preTy.preUU
        apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        exact 𝔓.2
⟩
-- ,
-- λ P => P.cons_D _ (𝔓.elim P) _ (P.PI_D _ _ _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) (Tm.VAR 0) (P.VAR0_D _ _ _ _ _) _ _ _) _ (P.EL_D _ _ _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) _ (P.VAR0_D _ _ _ _ _) _ _ _) _ _ _)))
--⟩
