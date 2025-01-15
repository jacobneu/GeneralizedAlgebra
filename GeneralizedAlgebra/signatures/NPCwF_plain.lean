import GeneralizedAlgebra.signature_plain

def 𝔑𝔓ℭ𝔴𝔉_data := [namedGAT|
    Con : U,
    Sub : Con ⇒ Con ⇒ U,
    id  : (X : Con) ⇒ Sub X X,
    comp  : (X :Con) ⇒ (Y : Con) ⇒ (Z : Con) ⇒
            Sub Y Z ⇒ Sub X Y ⇒ Sub X Z,
    lunit : (X : Con) ⇒ (Y : Con) ⇒ (f : Sub X Y) ⇒
            comp (id Y) f ≡ f,
    runit : (X : Con) ⇒ (Y : Con) ⇒ (f : Sub X Y) ⇒
            comp f (id X) ≡ f,
    assoc : (W:Con) ⇒ (X:Con) ⇒ (Y:Con) ⇒ (Z:Con) ⇒ (e : Sub W X) ⇒
            (f : Sub X Y) ⇒ (g : Sub Y Z) ⇒
            comp g (comp f e) ≡ comp (comp g f) e,
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
              ≡ substTy Θ Γ (comp γ δ) A,
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
              ≡ substTm Θ Γ A (comp γ δ) t,
    ext     : ( Γ : Con) ⇒ Ty Γ ⇒ Con,
    pair    : (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              Tm Δ (substTy Δ Γ γ A) ⇒
              Sub Δ (ext Γ A),
    pair_nat: (Θ:Con)⇒ (Δ:Con)⇒ (Γ : Con) ⇒ (A : Ty Γ) ⇒
              (γ : Sub Δ Γ) ⇒
              (t : Tm Δ (substTy Δ Γ γ A)) ⇒
              (δ : Sub Θ Δ) ⇒
              comp (pair Δ Γ A γ t) δ
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
              ≡ σ,
    neg_Con    : Con ⇒ Con,
    neg_Sub    : (Δ:Con) ⇒  (Γ : Con ) ⇒ Sub Δ Γ ⇒
        Sub (neg_Con Δ) (neg_Con Γ),
    neg_Ty     : ( Γ : Con ) ⇒ Ty Γ ⇒ Ty Γ,
    neg_empty  : neg_Con empty ≡ empty,
    neg_id     : ( Γ : Con ) ⇒
        neg_Sub (id Γ) ≡ id (neg_Con Γ),
    neg_comp   : (Θ:Con) ⇒ (Δ:Con) ⇒ (Γ : Con ) ⇒
        (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
        neg_Sub (comp γ δ)
        ≡ comp (neg_Sub γ) (neg_Sub δ),
    neg_nat    : (Δ:Con) ⇒ (Γ : Con ) ⇒
        (γ : Sub Δ Γ) ⇒ (A : Ty Γ) ⇒
        neg_Ty Δ (substTy γ A)
        ≡ substTy γ (neg_Ty Γ A),
    invl_Con   : ( Γ : Con) ⇒ neg_Con(neg_Con Γ) ≡ Γ,
    invl_Sub   : (Δ:Con)⇒ (Γ : Con ) ⇒ (γ : Sub Δ Γ) ⇒
        neg_Sub(neg_Sub γ) ≡ γ,
    invl_Ty    : ( Γ : Con ) ⇒ (A : Ty Γ) ⇒
        neg_Ty (neg_Ty A) ≡ A,
    isneut_Con : Con ⇒ U,
    isneut_Con_prop : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ (Γn' : isneut_Con Γ) ⇒  Γn ≡ Γn',
    isneut_Ty : (Γ:Con) ⇒ Ty Γ ⇒ U,
    isneut_Ty_prop : (Γ:Con) ⇒ (A : Ty Γ) ⇒ (An : isneut_Ty Γ A) ⇒ (An' : isneut_Ty Γ A) ⇒  An ≡ An',

    empty_isneut : isneut_Con empty,
    neg_Con_isneut   : (Γ:Con) ⇒ isneut_Con Γ ⇒ isneut_Con (neg_Con Γ),
    neg_Ty_isneut : (Γ:Con) ⇒ (A : Ty Γ) ⇒ isneut_Ty Γ A ⇒ isneut_Ty Γ (neg_Ty Γ A),
    subst_isneut : (Δ:Con) ⇒ (Γ:Con) ⇒ (σ : Sub Δ Γ) ⇒ (A : Ty Γ) ⇒ isneut_Ty Γ A ⇒ isneut_Ty Δ (substTy Δ Γ σ A),
    ext_isneut : (Γ : Con) ⇒ (A : Ty Γ) ⇒ isneut_Con Γ ⇒ isneut_Ty Γ A ⇒ isneut_Con (ext Γ A),

    ee : (Γ:Con) ⇒ isneut_Con Γ ⇒ Sub Γ (neg_Con Γ),
    -- ee_neg : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ neg_Sub (ee Γ Γn) ≡ ee (neg_Con Γ) (neg_Con_isneut Γ Γn),
    ee_β : (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ comp Γ (neg_Con Γ) Γ (ee Γ Γn) (neg_Sub (ee Γ Γn)) ≡ id Γ,
    ee_η : (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ comp (neg_Con Γ) Γ (neg_Con Γ)  (neg_Sub (ee Γ Γn)) (ee Γ Γn) ≡ id (neg_Con Γ),
    ee_nat : (Δ : Con) ⇒ (Δn : isneut_Con Δ) ⇒ (Γ : Con) ⇒ (Γn : isneut_Con Γ) ⇒ (σ : Sub Δ Γ) ⇒
        σ ≡ comp Δ (neg_Con Γ) Γ (neg_Sub (ee Γ Γn)) (comp Δ (neg_Con Δ) (neg_Con Γ) (neg_Sub σ) (ee Δ Δn)),

    minus : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ (A : Ty Γ) ⇒ Tm Γ A ⇒ Tm Γ (neg_Ty Γ A),
    minus_inv : (Γ:Con) ⇒ (Γn : isneut_Con Γ) ⇒ (A : Ty Γ) ⇒ (t : Tm Γ A) ⇒ minus Γ Γn (neg_Ty A) (minus Γ Γn A t) ≡ t
    -- TODO: finish
]

def 𝔑𝔓ℭ𝔴𝔉 : Con := 𝔑𝔓ℭ𝔴𝔉_data.1
def NPCwF_names := 𝔑𝔓ℭ𝔴𝔉_data.2.1
def NPCwF_topnames := 𝔑𝔓ℭ𝔴𝔉_data.2.2

#eval Con_toString 𝔑𝔓ℭ𝔴𝔉
#eval NPCwF_names
#eval List.length NPCwF_topnames
#eval len 𝔑𝔓ℭ𝔴𝔉
#eval Alg 𝔑𝔓ℭ𝔴𝔉 NPCwF_names true
