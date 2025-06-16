import GeneralizedAlgebra.signatures.pointed

def 𝔑 : GAT := ⟨
⦃
    Nat   : U,
    zero  : Nat,
    succ  : Nat ⇒ Nat
⦄,
λ P => P.cons_D _ (𝔓.elim P) _ (P.PI_D _ _ _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) (Tm.VAR 0) (P.VAR0_D _ _ _ _ _) _ _ _) _ (P.EL_D _ _ _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) _ (P.VARSUCC_D _ _ Ty.UU (P.UU_D _ _) _ (P.VAR0_D _ _ _ _ _) _ _ _) _ _ _)))
⟩
