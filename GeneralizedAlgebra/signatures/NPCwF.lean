import GeneralizedAlgebra.signature_plain

def 𝔑𝔓ℭ𝔴𝔉 := ⦃
    include 𝔓ℭ𝔴𝔉 as (Con,Sub,id,comp,empty,_,
        Ty,substTy,Tm,substTm,ext,pair,π₁,π₂,
        neg_Con,neg_Sub,neg_Ty);
    isneut_Con : Con ⇒ U,
    isneut_Con_prop : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ (Γn' : isneut_Con Γ) ⇒  Γn ≡ Γn',
    isneut_Ty : (Γ:Con) ⇒ Ty Γ ⇒ U,
    isneut_Ty_prop : (Γ:Con) ⇒ (A : Ty Γ) ⇒ (An : isneut_Ty Γ A) ⇒ (An' : isneut_Ty Γ A) ⇒  An ≡ An',

    empty_isneut : isneut_Con empty,
    neg_Con_isneut   : (Γ:Con) ⇒ isneut_Con Γ ⇒ isneut_Con (neg_Con Γ),
    neg_Ty_isneut : (Γ:Con) ⇒ (A : Ty Γ) ⇒ isneut_Ty Γ A ⇒ isneut_Ty Γ (neg_Ty Γ A),
    subst_isneut : (Δ:Con) ⇒ (Γ:Con) ⇒ (σ : Sub Δ Γ) ⇒ (A : Ty Γ) ⇒ isneut_Ty Γ A ⇒ isneut_Ty Δ (substTy Δ Γ σ A),
    ext_isneut : (Γ : Con) ⇒ (A : Ty Γ) ⇒ isneut_Con Γ ⇒ isneut_Ty Γ A ⇒ isneut_Con (ext Γ A),

    minus : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ (A : Ty Γ) ⇒ Tm Γ A ⇒ Tm Γ (neg_Ty Γ A),
    minus_inv : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒ minus Γ Γn (neg_Ty A) (minus Γ Γn A t) ≡ t,

    e : (Γ:Con) ⇒ isneut_Con Γ ⇒ Sub (neg_Con Γ) Γ,
    e_neg : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ neg_Sub (e Γ Γn) ≡ e (neg_Con Γ) (neg_Con_isneut Γ Γn),
    e_β : (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ comp (neg_Con Γ) Γ (neg_Con Γ) (e Γ Γn) (neg_Sub (e Γ Γn)) ≡ id (neg_Con Γ),
    e_η : (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ comp Γ (neg_Con Γ) Γ (neg_Sub (e Γ Γn)) (e Γ Γn) ≡ id Γ,
    e_nat : (Δ : Con) ⇒ (Δn : isneut_Con Δ) ⇒ (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ (σ : Sub Δ Γ) ⇒
        σ ≡ comp Δ (neg_Con Γ) Γ (neg_Sub (e Γ Γn)) (comp Δ (neg_Con Δ) (neg_Con Γ) (neg_Sub σ) (e Δ Δn)),

    ee1 : (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ (A₀ : Ty Γ) ⇒
        Sub (neg_Con (ext (neg_Con Γ) (substTy (neg_Con Γ) Γ (e Γ Γn) (neg_Ty A₀)))) (ext Γ A₀),

    ee2 : (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ (A₁ : Ty Γ) ⇒ (A₀ : Ty Γ) ⇒
        Sub
            (neg_Con
                (ext
                    (ext
                        (neg_Con Γ)
                        (substTy (neg_Con Γ) Γ (e Γ Γn) (neg_Ty A₁))
                    )
                    (substTy (ext (neg_Con Γ) (substTy (neg_Con Γ) Γ (e Γ Γn) (neg_Ty A₁))) Γ
                        (comp
                            (e Γ Γn)
                            (π₁ (id (ext (neg_Con Γ) (substTy (neg_Con Γ) Γ (e Γ Γn) (neg_Ty A₁)))))
                        )
                        (neg_Ty A₀)
                    )
                )
            )
            (ext (ext Γ A₁) A₀)
    -- TODO: finish
⦄
