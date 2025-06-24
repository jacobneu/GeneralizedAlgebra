import GeneralizedAlgebra.signatures.set


-- def pointedLemma (P : indData) :
--   P.Tm_D
--     [Ty.UU]
--     (P.cons_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D))
--     (Ty.EL (Tm.VAR 0))
--     (P.EL_D [Ty.UU] (P.cons_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D)) (Tm.VAR 0) (P.VAR0_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D) (P.UU_D [Ty.UU] (P.cons_D [] P.nil_D Ty.UU (P.UU_D [] P.nil_D)))))
--     (Tm.VAR 0)
--   := by

--     have helper := P.VAR0_D EMPTY P.nil_D Ty.UU (P.UU_D _ _) (P.UU_D _ _)
--     -- rw [WkTy] at helper
--     sorry



def 𝔓 : GAT :=
  ⦃ X : U, x : X ⦄
  -- ,
  -- λ P => P.cons_D _ (𝔖𝔢𝔱.elim P) _ (P.EL_D _ _ _ (P.VAR0_D _ _ _ _ _))
  -- by
  --   intro P
  --   apply P.cons_D
  --   apply P.EL_D
  --   have helper := P.VAR0_D EMPTY P.nil_D Ty.UU (P.UU_D _ _)
  --   rw [WkTy] at helper
  --   apply helper
-- #reduce 𝔓.elim
