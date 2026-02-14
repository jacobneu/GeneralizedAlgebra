import GeneralizedAlgebra.signatures.pointed

def 𝔅_data : GATdata := --⟨
  [GATdata| X : U, x : X, x' : X ]--,
  -- λ P => P.cons_D _ (𝔓.elim P) _ (P.EL_D _ _ _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) (Tm.VAR 0) (P.VAR0_D _ _ _ _ _) _ _ _))
  -- ⟩

def 𝔅 : GAT := ⟨
  𝔅_data,
  by
    apply wellCon.wellCons
    apply wellTy.wellEL
    apply @wellTm.wellWkTm _ preTy.preUU
    apply wellTm.wellZero
    apply wellTy.wellUU
    exact 𝔓.2
⟩
