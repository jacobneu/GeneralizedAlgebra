import GeneralizedAlgebra.nouGAT


def pointedLemma (P : indData) :
  P.Tm_D
    [Ty.UU]
    (P.cons_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D))
    (Ty.EL (Tm.VAR 0))
    (P.EL_D [Ty.UU] (P.cons_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D)) (Tm.VAR 0) (P.VAR0_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D) (P.UU_D [Ty.UU] (P.cons_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D)))))
    (Tm.VAR 0)
  := by

    have helper := P.VAR0_D EMPTY P.nil_D Ty.UU (P.UU_D _ _) (P.UU_D _ _)
    -- rw [WkTy] at helper
    sorry



def 𝔓 : GAT := ⟨
  ⦃ X : U, x : X ⦄,

  by
    intro P
    apply P.cons_D
    apply P.EL_D
    have helper := P.VAR0_D EMPTY P.nil_D Ty.UU (P.UU_D _ _)
    rw [WkTy] at helper
    apply helper
  ⟩
