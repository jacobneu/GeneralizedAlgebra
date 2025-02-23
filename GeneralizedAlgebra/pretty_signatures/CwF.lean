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
              (γ : Sub Δ Γ) ⇒ (δ : Sub Θ Δ) ⇒
              substTy Δ Γ γ (substTy Θ Δ δ A)
              ≡ substTy Θ Γ (comp γ δ) A,
    Tm      : ( Γ : Con) ⇒ Ty Γ ⇒ U,
    substTm : {Δ Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Γ A ⇒ Tm Δ (substTy Δ Γ γ A),
    idTm    : {Γ : Con} ⇒ {A : Ty Γ} ⇒ (t : Tm Γ A)
              substTm (id Γ) t      #⟨idTy A⟩
              ≡ t,
    compTm  : {Θ Δ Γ : Con} ⇒
              {A : Ty Γ} ⇒ (t : Tm Γ A) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTm γ (substTm δ t)     #⟨compTy A γ δ⟩
              ≡ substTm (comp γ δ) t,
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
              ≡ pair (comp γ δ) (substTm δ t  #⟨compTy A γ δ⟩),
    p       : {Γ : Con} ⇒ (A : Ty Γ) ⇒ Sub (ext Γ A) Γ,
    v       : {Γ : Con} ⇒ (A : Ty Γ) ⇒
              Tm (ext Γ A) (substTy (p A) A),
    ext_β₁  : {Δ : Con} ⇒ {Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy γ A)) ⇒
              comp (p A) (pair γ t) ≡ γ,
    ext_β₂  : {Δ : Con} ⇒ {Γ : Con} ⇒ {A : Ty Γ} ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy γ A)) ⇒
              substTm (pair γ t) (v A)  #⟨compTy A (p A) (pair γ t); ext_β₁ γ t⟩
              ≡ t,
    ext_η   : (Γ : Con) ⇒ (A : Ty Γ) ⇒
              pair (p Γ A) (v Γ A) ≡ id (ext Γ A)
⦄
