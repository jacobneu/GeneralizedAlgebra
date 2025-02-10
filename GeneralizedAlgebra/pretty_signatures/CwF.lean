import GeneralizedAlgebra.pretty_signatures.category

def ℭ𝔴𝔉 : GAT := ⦃
  include ℭ𝔞𝔱 as (Con,Sub,comp,id);
    empty : Con,
    ε : ( Γ : Con) ⇒ Sub Γ empty,
    ε_η : ( Γ : Con) ⇒ (f : Sub Γ empty) ⇒ f ≡ (ε Γ),
    Ty      : Con ⇒ U,
    substTy : {Δ Γ : Con} ⇒ Sub Δ Γ ⇒ Ty Γ ⇒ Ty Δ,
    idTy    : {Γ : Con} ⇒ (A : Ty Γ) ⇒
              substTy (id Γ) A ≡ A,
    compTy  : {Θ Δ Γ : Con} ⇒ (A : Ty Γ)
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTy Δ Γ γ (substTy Θ Δ δ A)
              ≡ substTy Θ Γ (comp γ δ) A,
    Tm      : ( Γ : Con) ⇒ Ty Γ ⇒ U,
    substTm : {Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Γ A ⇒ Tm Δ (substTy Δ Γ γ A),
    idTm    : {Γ : Con} ⇒ {A : Ty Γ} ⇒ (t : Tm Γ A)
              substTm (id Γ) t ≡ t,
    compTm  : {Θ Δ Γ : Con} ⇒
              {A : Ty Γ} ⇒ (t : Tm Γ A) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTm γ (substTm δ t) ≡ substTm (comp γ δ) t,
    ext     : ( Γ : Con) ⇒ Ty Γ ⇒ Con,
    pair    : {Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Δ (substTy γ A) ⇒
              Sub Δ (ext Γ A),
    pair_nat: {Θ Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy γ A)) ⇒
              (δ : Sub Θ Δ) ⇒
              comp (pair γ t) δ
              ≡ pair (comp γ δ) (substTm δ t),
    π₁      : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              Sub Δ (ext Γ A) ⇒ Sub Δ Γ,
    π₂      : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (σ : Sub Δ (ext Γ A)) ⇒
              Tm Δ (substTy Δ Γ (pi1 Δ Γ A σ) A),
    ext_β₁  : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              π₁ Δ Γ A (pair Δ Γ A γ t) ≡ γ,
    ext_β₂  : ( Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              π₂ Δ Γ A (pair Δ Γ A γ t) ≡ t,
    ext_η   : (Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (σ : Sub Δ (ext Γ A)) ⇒
              pair Δ Γ A (π₁ Δ Γ A σ) (π₂ Δ Γ A σ)
              ≡ σ
⦄
