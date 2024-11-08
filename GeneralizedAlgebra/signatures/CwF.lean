import GeneralizedAlgebra.signature

def ℭ𝔴𝔉 : GAT_sig :=
  extend ℭ𝔞𝔱 = (Con,Sub,comp,id,_,_,_) plus
    Ty      : Con ⇒ U,
    substTy : ( Δ Γ : Con) ⇒ Sub Δ Γ ⇒ Ty Γ ⇒ Ty Δ,
    idTy    : ( Γ : Con) ⇒ (A : Ty Γ) ⇒
              substTy Γ Γ (id Γ) A ≡ A,
    compTy  : ( Θ Δ Γ : Con) ⇒ (A : Ty Γ)
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTy Δ Γ γ (substTy Θ Δ δ A)
              ≡ substTy Θ Γ (comp γ δ) A,
    Tm      : ( Γ : Con) ⇒ Ty Γ ⇒ U,
    substTm : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Γ A ⇒ Tm Δ (substTy Δ Γ γ A),
    idTm    : ( Γ : Con) ⇒ (A : Ty Γ) ⇒ (t : Tm Γ A)
              substTm Γ Γ A (id Γ) t ≡ t,
    compTm  : ( Θ Δ Γ : Con) ⇒
              (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTm Δ Γ A γ
                (substTm Θ Δ (substTy Δ Γ γ A) δ t)
              ≡ substTm Θ Γ A (comp γ δ) t
