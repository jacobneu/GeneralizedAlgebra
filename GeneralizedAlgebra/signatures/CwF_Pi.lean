import GeneralizedAlgebra.nouGAT

def ℭ𝔴𝔉pi : GAT := ⦃
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
              substTm Γ Γ A (id Γ) t     #⟨idTy Γ A⟩
              ≡ t,
    compTm  : (Θ:Con)⇒ (Δ:Con)⇒ (Γ : Con) ⇒
              (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒
              (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
              substTm Δ Γ A γ
                (substTm Θ Δ (substTy Δ Γ γ A) δ t)      #⟨compTy Θ Δ Γ A γ δ⟩
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
              ≡ pair Θ Γ A (comp Θ Δ Γ γ δ) (substTm Θ Δ (substTy Δ Γ γ A) δ t   #⟨compTy Θ Δ Γ A γ δ⟩),
    p      : (Γ : Con) ⇒ (A : Ty Γ) ⇒ Sub (ext Γ A) Γ,
    v      : (Γ : Con) ⇒ (A : Ty Γ) ⇒
              Tm (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A),
    ext_β₁  : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              comp Δ (ext Γ A) Γ (p Γ A) (pair Δ Γ A γ t) ≡ γ,
    ext_β₂  : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              substTm Δ (ext Γ A) (substTy Δ Γ γ A) (pair Δ Γ A γ t) (v Γ A)
                  #⟨compTy Δ (ext Γ A) Γ A (p Γ A) (pair Δ Γ A γ t)⟩  #⟨ext_β₁ Δ Γ A γ t⟩
              ≡ t,
    ext_η   : (Γ : Con) ⇒ (A : Ty Γ) ⇒
              pair (ext Γ A) Γ A (p Γ A) (v Γ A)
              ≡ id (ext Γ A),

    Pi : (Γ : Con) ⇒ (A : Ty Γ) ⇒ Ty (ext Γ A) ⇒ Ty Γ,
    Pi_stab : (Δ : Con) ⇒ (Γ : Con) ⇒ (σ : Sub Δ Γ) ⇒
        (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        substTy Δ Γ σ (Pi Γ A B)
        ≡ Pi Δ (substTy Δ Γ σ A)
                (substTy
                    (ext Δ (substTy Δ Γ σ A))
                    (ext Γ A)
                    (pair
                        (ext Δ (substTy Δ Γ σ A))
                        Γ
                        A
                        (comp (ext Δ (substTy Δ Γ σ A)) Δ Γ σ (p Δ (substTy Δ Γ σ A)))
                        (v Δ (substTy Δ Γ σ A)))
                    B),
    lam : (Γ : Con) ⇒ (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        Tm (ext Γ A) B ⇒ Tm Γ (Pi Γ A B),
    app : (Γ : Con) ⇒ (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        Tm Γ (Pi Γ A B) ⇒ (t : Tm Γ A) ⇒
        Tm Γ (substTy Γ (ext Γ A) (pair Γ Γ A (id Γ) (t #⟨⁻¹ idTy Γ A⟩)) B),
    lam_stab : (Δ : Con) ⇒ (Γ : Con) ⇒ (σ : Sub Δ Γ) ⇒
        (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        (t : Tm (ext Γ A) B) ⇒
        substTm Δ Γ σ (Pi Γ A B) (lam Γ A B t)
            #⟨Pi_stab Δ Γ σ A B⟩
        ≡ (lam Δ (substTy Δ Γ σ A) (substTy (ext Δ (substTy Δ Γ σ A)) (ext Γ A) (pair (ext Δ (substTy Δ Γ σ A)) Γ A (comp (ext Δ (substTy Δ Γ σ A)) Δ Γ σ (p Δ (substTy Δ Γ σ A))) (v Δ (substTy Δ Γ σ A))) B)
                (substTm (ext Δ (substTy Δ Γ σ A)) (ext Γ A)
                    (pair (ext Δ (substTy Δ Γ σ A)) Γ A (comp (ext Δ (substTy Δ Γ σ A)) Δ Γ σ (p Δ (substTy Δ Γ σ A))) (v Δ (substTy Δ Γ σ A)))
                B t)),
    Pi_β : (Γ : Con) ⇒ (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        (F : Tm (ext Γ A) B) ⇒ (t : Tm Γ A) ⇒
        app Γ A B (lam Γ A B F) t ≡ substTm Γ (ext Γ A) B (pair Γ Γ A (id Γ) (t #⟨⁻¹ idTy Γ A⟩)) F,
    Pi_η : (Γ : Con) ⇒ (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        (f : Tm Γ (Pi Γ A B)) ⇒
        lam Γ A B (app      (ext Γ A)
                            (substTy (ext Γ A) Γ (p Γ A) A) -- : Ty (ext Γ A)

                (substTy
                    (ext (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A))
                    (ext Γ A)
                    (pair
                        (ext (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A))
                        Γ
                        A
                        (comp (ext (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A)) (ext Γ A) Γ (p Γ A) (p (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A)))
                        (v (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A)))
                    B) -- : Ty (ext (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A))
                            ((substTm (ext Γ A) Γ (p Γ A) (Pi Γ A B) f)  #⟨ Pi_stab (ext Γ A) Γ (p Γ A) A B ⟩) -- Tm (ext Γ A) (Pi (substTy (ext Γ A) Γ (p Γ A) A) )
                            (v Γ A) -- : Tm (ext Γ A) (substTy (ext Γ A) Γ (p Γ A) A)
                  )
        ≡ f
⦄
