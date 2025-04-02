import GeneralizedAlgebra.pretty_signatures.category

def ℭ𝔴𝔉 : GAT := ⦃
  include ℭ𝔞𝔱 as (Con,Sub,comp,id);
    empty   : Con,
    ε       : (Γ : Con) ⇒ Sub Γ empty,
    ε_η     : (Γ : Con) ⇒ (f : Sub Γ empty) ⇒
              f ≡ (ε Γ),
    Ty      : Con ⇒ U,
    substTy : {Δ Γ : Con} ⇒ Sub Δ Γ ⇒ Ty Γ ⇒ Ty Δ,
    idTy    : {Γ : Con} ⇒ (A : Ty Γ) ⇒
              substTy (id Γ) A ≡ A,
    compTy  : {Θ Δ Γ : Con} ⇒ (A : Ty Γ)
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTy γ (substTy δ A)
              ≡ substTy (comp γ δ) A,
    Tm      : (Γ : Con) ⇒ Ty Γ ⇒ U,
    substTm : {Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Γ A ⇒ Tm Δ (substTy γ A),
    idTm    : {Γ : Con} ⇒ {A : Ty Γ} ⇒ (t : Tm Γ A)
              substTm (id Γ) t      #⟨idTy A⟩
              ≡ t,
    compTm  : {Θ Δ Γ : Con} ⇒
              {A : Ty Γ} ⇒ (t : Tm Γ A) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTm γ (substTm δ t)
                  #⟨compTy A γ δ⟩
              ≡ substTm (comp γ δ) t,
    ext     : (Γ : Con) ⇒ Ty Γ ⇒ Con,
    pair    : {Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Δ (substTy γ A) ⇒
              Sub Δ (ext Γ A),
    pair_nat: {Θ Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy γ A)) ⇒
              (δ : Sub Θ Δ) ⇒
              comp (pair γ t) δ
              ≡ pair (comp γ δ)
                  (substTm δ t  #⟨compTy A γ δ⟩),
    p       : {Γ : Con} ⇒ (A : Ty Γ) ⇒
              Sub (ext Γ A) Γ
    v       : {Γ : Con} ⇒ (A : Ty Γ) ⇒
              Tm (ext Γ A) (substTy (p A) A),
    ext_β₁  : (Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy γ A)) ⇒
              comp (p A) (pair γ t) ≡ γ,
    ext_β₂  : (Δ Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy γ A)) ⇒
              substTm (pair γ t) (v A)
                  #⟨compTy A (p A) (pair γ t)⟩
                  #⟨ext_β₁ γ t⟩
              ≡ t,
    ext_η   : (Γ : Con) ⇒ (A : Ty Γ) ⇒
              pair (p A) (v A)
              ≡ id (ext Γ A)
⦄
