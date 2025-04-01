import GeneralizedAlgebra.signatures.pointed

def 𝔅 : GAT := ⟨
  ⦃ X : U, x : X, x' : X ⦄,

  by
    intro P
    apply P.cons_D
    apply P.EL_D
    rw [WkTm]
    have helper := P.VARSUCC_D [Ty.EL (Tm.VAR 0), Ty.UU] --[Ty.UU] (P.cons_D _ P.nil_D _ (P.UU_D _ _)) (Ty.EL (Tm.VAR 0)) (P.EL_D _ _ _ (P.VAR0_D _ _ _ _ _)) (Tm.VAR 0) Ty.UU (P.UU_D _ _)  -- (Ty.EL (Tm.VAR 1))
    -- rw [WkTm] at helper
    apply helper
    have helper' := P.VAR0_D EMPTY P.nil_D Ty.UU (P.UU_D _ _)
    rw [WkTy] at helper'
    apply helper'


  ⟩
