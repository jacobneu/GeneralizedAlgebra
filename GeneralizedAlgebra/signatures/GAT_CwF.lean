import GeneralizedAlgebra.nouGAT

def 𝔊𝔄𝔗ℭ𝔴𝔉_data : GATdata := [GATdata|
    Con : U,
    Ty : Con ⇒ U,
    Sub : Con ⇒ Con ⇒ U,
    Tm : (Γ : Con) ⇒ Ty Γ ⇒ U,
    empty : Con,
    ext : (Γ : Con) ⇒ Ty Γ ⇒ Con,
    substTy : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ Sub Γ Δ ⇒ Ty Γ,
    id : (Γ : Con) ⇒ Sub Γ Γ,
    comp : (Γ : Con) ⇒ (Θ : Con) ⇒ (Δ : Con) ⇒ Sub Θ Δ ⇒ Sub Γ Θ ⇒ Sub Γ Δ,
    ε : (Γ : Con) ⇒ Sub Γ empty,
    pair : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ Δ) ⇒ Tm Γ (substTy Γ Δ σ A) ⇒ Sub Γ (ext Δ A),
    π₁ : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ Sub Γ (ext Δ A) ⇒ Sub Γ Δ,
    π₂ : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ (ext Δ A)) ⇒ Tm Γ (substTy Γ Δ (π₁ Γ Δ A σ) A),
    substTm : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ Δ) ⇒ Tm Δ A ⇒ Tm Γ (substTy Γ Δ σ A),
    idTy : (Γ : Con) ⇒ (A : Ty Γ) ⇒ substTy Γ Γ (id Γ) A ≡ A,
    compTy : (Γ : Con) ⇒ (Θ : Con) ⇒ (Δ : Con) ⇒ (σ : Sub Θ Δ) ⇒ (δ : Sub Γ Θ) ⇒ (A : Ty Δ) ⇒ substTy Γ Δ δ (substTy Θ Δ σ A) ≡ substTy Γ Δ (comp Γ Θ Δ σ δ) A,
    idTm    : (Γ : Con) ⇒ (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒ substTm Γ Γ A (id Γ) t #⟨idTy Γ A⟩ ≡ t,
    compTm  : (Θ : Con) ⇒ (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒ (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒ substTm Δ Γ A γ (substTm Θ Δ (substTy Δ Γ γ A) δ t) #⟨compTy Θ Δ Γ A γ δ⟩ ≡ substTm Θ Γ A (comp Θ Δ Γ γ δ) t,
    ass : (Ξ : Con) ⇒ (Θ : Con) ⇒ (Δ : Con) ⇒ (Γ : Con) ⇒ (ϑ : Sub Ξ Θ) ⇒ (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒ comp Ξ Θ Γ γ (comp Ξ Θ Δ ϑ δ) ≡ comp Ξ Δ Γ (comp Θ Δ Γ δ γ) ϑ,
    idl : (Δ : Con) ⇒ (Γ : Con) ⇒ (γ : Sub Δ Γ) ⇒ comp Δ Γ Γ (id Γ) γ ≡ γ,
    idr : (Δ : Con) ⇒ (Γ : Con) ⇒ (γ : Sub Δ Γ) ⇒ comp Δ Δ Γ γ (id Δ) ≡ γ,
    ηε : (Γ : Con) ⇒ (f : Sub Γ empty) ⇒ f ≡ (ε Γ),
    ext_β₁ : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ Δ) ⇒ (t : Tm Γ (substTy Γ Δ σ A)) ⇒ π₁ Γ Δ A (pair Γ Δ A σ t) ≡ σ,
    ext_β₁ : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ Δ) ⇒ (t : Tm Γ (substTy Γ Δ σ A)) ⇒ π₂ Γ Δ A (pair Γ Δ A σ t) #⟨ ext_β₁ Γ Δ A σ t ⟩ ≡ t,
    ext_η : (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ (ext Δ A)) ⇒ pair Γ Δ A (π₁ Γ Δ A σ) (π₂ Γ Δ A σ) ≡ σ,
    ext_subst : (Θ : Con) ⇒ (Γ : Con) ⇒ (Δ : Con) ⇒ (A : Ty Δ) ⇒ (σ : Sub Γ Δ) ⇒ (t : Tm Γ (substTy Γ Δ σ A)) ⇒ (γ : Sub Θ Γ) ⇒
        comp Θ Γ (ext Δ A) (pair Γ Δ A σ t) γ
        ≡ pair Θ Δ A (comp Θ Γ Δ σ γ) (substTm Θ Γ (substTy Γ Δ σ A) γ t),
    u : (Γ : Con) ⇒ Ty Γ,
    el : (Γ : Con) ⇒ Tm Γ (u Γ) ⇒ Ty Γ,
    u_subst : (Γ : Con) ⇒ (Δ : Con) ⇒ (σ : Sub Γ Δ) ⇒ substTy Γ Δ (u Δ) σ ≡ u Γ,
    el_subst : (Γ : Con) ⇒ (Δ : Con) ⇒ (σ : Sub Γ Δ) ⇒ (a : Tm Δ (u Δ)) ⇒ substTy Γ Δ (el Δ a) σ ≡ el Γ (substTm Γ Δ (u Δ) σ a),
    Pi : (Γ : Con) ⇒ (a : Tm Γ (u Γ)) ⇒ Ty (ext Γ (el Γ a)) ⇒ Ty Γ,
    app : (Γ : Con) ⇒ (a : Tm Γ (u Γ)) ⇒ (B : Ty (ext Γ (el Γ a))) ⇒ Tm Γ (Pi Γ a B) ⇒ Tm (ext Γ (el Γ a)) B,
    Pi_subst : (Γ : Con) ⇒ (Δ : Con) ⇒ (a : Tm Δ (u Δ)) ⇒ (B : Ty (ext Δ (el Δ a))) ⇒ (σ : Sub Γ Δ) ⇒
        substTy Γ Δ (Pi Δ a B) σ ≡ Pi Γ (substTm Γ Δ (u Δ) σ a) (substTy (ext Γ (el Γ (substTm Γ Δ (u Δ) σ a))) (ext Δ (el Δ a)) B (pair (ext Γ (el Γ (substTm Γ Δ (u Δ) σ a))) Δ (el Δ a) (comp (ext Γ (el Γ (substTm Γ Δ (u Δ) σ a))) Γ Δ σ (π₁ (ext Γ (el Γ (substTm Γ Δ (u Δ) σ a))) Γ (el Γ (substTm Γ Δ (u Δ) σ a)) (id (ext Γ (el Γ (substTm Γ Δ (u Δ) σ a)))))) (π₂ (ext Δ (el Δ a)) Δ (el Δ a) (id (ext Δ (el Δ a)))))),
    Id : (Γ : Con) ⇒ (a : Tm Γ (u Γ)) ⇒ Tm Γ (el Γ a) ⇒ Tm Γ (el Γ a) ⇒ Ty Γ,
    reflect : (Γ : Con) ⇒ (a : Tm Γ (u Γ)) ⇒ (s : Tm Γ (el Γ a)) ⇒ (t : Tm Γ (el Γ a)) ⇒ Tm Γ (Id Γ a s t) ⇒ s ≡ t,
    Id_subst : (Γ : Con) ⇒ (Δ : Con) ⇒ (a : Tm Δ (u Δ)) ⇒ (s : Tm Δ (el Δ a)) ⇒ (t : Tm Δ (el Δ a)) ⇒ (σ : Sub Γ Δ) ⇒
        substTy Γ Δ (Id Δ a s t) σ ≡ Id Γ (substTm Γ Δ (u Δ) σ a ) (substTm Γ Δ (el Δ a) σ s) (substTm Γ Δ (el Δ a) σ t)
]
