import GeneralizedAlgebra.nouGAT

def 𝔓ℭ𝔴𝔉 : GAT := ⦃
    Con : U,
    Sub : Con ⇒ Con ⇒ U,
    id  : ( Γ : Con) ⇒ Sub Γ Γ,
    comp  : (Θ :Con) ⇒ (Δ : Con) ⇒ (Γ : Con) ⇒
            Sub Δ Γ ⇒ Sub Θ Δ ⇒ Sub Θ Γ,
    lunit : (Δ : Con) ⇒ (Γ : Con) ⇒ ( γ : Sub Δ Γ) ⇒
            comp Δ Γ Γ (id Γ) γ ≡ γ,
    runit : (Δ : Con) ⇒ (Γ : Con) ⇒ ( γ : Sub Δ Γ) ⇒
            comp Δ Δ Γ γ (id Δ) ≡ γ,
    assoc : (Ξ:Con) ⇒ (Θ:Con) ⇒ (Δ:Con) ⇒ (Γ:Con) ⇒ (ϑ : Sub Ξ Θ) ⇒
            (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
            comp Ξ Θ Γ γ (comp Ξ Θ Δ ϑ δ) ≡ comp Ξ Δ Γ (comp Θ Δ Γ δ γ) ϑ,
    empty : Con,
    ε : (Γ : Con) ⇒ Sub Γ empty,
    ηε : (Γ : Con) ⇒ (f : Sub Γ empty) ⇒ f ≡ (ε Γ),
    Ty      : Con ⇒ U,
    substTy : (Δ:Con)⇒ (Γ : Con) ⇒ Sub Δ Γ ⇒ Ty Γ ⇒ Ty Δ,
    idTy    : (Γ : Con) ⇒ (A : Ty Γ) ⇒
              substTy Γ Γ (id Γ) A ≡ A,
    compTy  : (Θ:Con)⇒ (Δ:Con)⇒  (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTy Δ Γ γ (substTy Θ Δ δ A)
              ≡ substTy Θ Γ (comp Θ Δ Γ γ δ) A,
    Tm      : (Γ : Con) ⇒ Ty Γ ⇒ U,
    substTm : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Γ A ⇒ Tm Δ (substTy Δ Γ γ A),
    idTm    : ( Γ : Con) ⇒ (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒
              substTm Γ Γ A (id Γ) t ≡ t,
    compTm  : (Θ:Con)⇒ (Δ:Con)⇒ (Γ : Con) ⇒
              (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTm Δ Γ A γ
                (substTm Θ Δ (substTy Δ Γ γ A) δ t)
              ≡ substTm Θ Γ A (comp Θ Δ Γ γ δ) t,
    ext     : ( Γ : Con) ⇒ Ty Γ ⇒ Con,
    pair    : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Δ (substTy Δ Γ γ A) ⇒
              Sub Δ (ext Γ A),
    pair_nat: (Θ:Con)⇒ (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              (δ : Sub Θ Δ) ⇒
              comp Θ Δ (ext Γ A) (pair Δ Γ A γ t) δ
              ≡ pair Θ Γ A (comp Θ Δ Γ γ δ) (substTm Θ Δ (substTy Δ Γ γ A) δ t),
    π₁      : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              Sub Δ (ext Γ A) ⇒ Sub Δ Γ,
    π₂      : (Δ:Con) ⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (σ : Sub Δ (ext Γ A)) ⇒
              Tm Δ (substTy Δ Γ (π₁ Δ Γ A σ) A),
    ext_β₁  : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              π₁ Δ Γ A (pair Δ Γ A γ t) ≡ γ,
    ext_β₂  : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              π₂ Δ Γ A (pair Δ Γ A γ t) ≡ t,
    ext_η   : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (σ : Sub Δ (ext Γ A)) ⇒
              pair Δ Γ A (π₁ Δ Γ A σ) (π₂ Δ Γ A σ)
              ≡ σ,
    neg_Con    : Con ⇒ Con,
    neg_Sub    : (Δ:Con) ⇒  (Γ : Con ) ⇒ Sub Δ Γ ⇒
        Sub (neg_Con Δ) (neg_Con Γ),
    neg_Ty     : ( Γ : Con ) ⇒ Ty Γ ⇒ Ty Γ,
    neg_empty  : neg_Con empty ≡ empty,
    neg_id     : ( Γ : Con ) ⇒
        neg_Sub Γ Γ (id Γ) ≡ id (neg_Con Γ),
    neg_comp   : (Θ:Con) ⇒ (Δ:Con) ⇒ (Γ : Con) ⇒
        (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
        neg_Sub Θ Γ (comp Θ Δ Γ γ δ)
        ≡ comp (neg_Con Θ) (neg_Con Δ) (neg_Con Γ) (neg_Sub Δ Γ γ) (neg_Sub Θ Δ δ),
    neg_nat    : (Δ:Con) ⇒ (Γ : Con) ⇒
        (γ : Sub Δ Γ) ⇒ (A : Ty Γ) ⇒
        neg_Ty Δ (substTy Δ Γ γ A)
        ≡ substTy Δ Γ γ (neg_Ty Γ A),
    invl_Con   : ( Γ : Con) ⇒ neg_Con(neg_Con Γ) ≡ Γ,
    invl_Sub   : (Δ:Con)⇒ (Γ : Con ) ⇒ (γ : Sub Δ Γ) ⇒
        neg_Sub (neg_Con Δ) (neg_Con Γ) (neg_Sub Δ Γ γ) ≡ γ,
    invl_Ty    : ( Γ : Con ) ⇒ (A : Ty Γ) ⇒
        neg_Ty Γ (neg_Ty Γ A) ≡ A
⦄
