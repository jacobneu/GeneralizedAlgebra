import GeneralizedAlgebra.signature_plain

def ℭ𝔴𝔉 : Con := ⦃
    Con : U,
    Sub : Con ⇒ Con ⇒ U,
    id  : (X : Con) ⇒ Sub X X,
    comp  : (X :Con) ⇒ (Y : Con) ⇒ (Z : Con) ⇒
            Sub Y Z ⇒ Sub X Y ⇒ Sub X Z,
    lunit : (X : Con) ⇒ (Y : Con) ⇒ (f : Sub X Y) ⇒
            comp X Y Y (id Y) f ≡ f,
    runit : (X : Con) ⇒ (Y : Con) ⇒ (f : Sub X Y) ⇒
            comp X X Y f (id X) ≡ f,
    assoc : (W:Con) ⇒ (X:Con) ⇒ (Y:Con) ⇒ (Z:Con) ⇒ (e : Sub W X) ⇒
            (f : Sub X Y) ⇒ (g : Sub Y Z) ⇒
            comp W X Z g (comp W X Y f e) ≡ comp W Y Z (comp X Y Z g f) e,
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
              ≡ pair Θ Γ A (comp γ δ) (substTm Θ Δ (substTy Δ Γ γ A) δ t),
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
              ≡ σ
⦄
#eval Con_toString ℭ𝔴𝔉
#eval Alg ℭ𝔴𝔉
