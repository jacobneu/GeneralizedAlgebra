import GeneralizedAlgebra.signature

def ℭ𝔴𝔉 : GAT_sig :=
  include ℭ𝔞𝔱 as (Con,Sub,comp,id,_,_,_);
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
              ≡ substTm Θ Γ A (comp γ δ) t,
    ext     : ( Γ : Con) ⇒ Ty Γ ⇒ Con,
    pair    : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Δ (substTy Δ Γ γ A) ⇒
              Sub Δ (ext Γ A),
    π₁      : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              Sub Δ (ext Γ A) ⇒ Sub Δ Γ,
    π₂      : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (σ : Sub Δ (ext Γ A)) ⇒
              Tm Δ (substTy Δ Γ (pi1 Δ Γ A σ) A),
    ext_β₁  : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              pi1 Δ Γ A (pair Δ Γ A γ t) ≡ γ,
    ext_β₂  : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              pi2 Δ Γ A (pair Δ Γ A γ t) ≡ t
    ext_η   : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (σ : Sub Δ (ext Γ A)) ⇒
              pair Δ Γ A (pi1 Δ Γ A σ) (pi2 Δ Γ A σ)
              ≡ σ
