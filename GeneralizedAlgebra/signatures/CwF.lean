import GeneralizedAlgebra.nouGAT

def ℭ𝔴𝔉 : GAT := ⦃
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
              ≡ σ
⦄

def CwF_inlinenames := [
    "Con",
    "Sub",
    "Γ",
    "id",
    "Θ",
    "Δ",
    "Γ",
    "comp",
    "Δ",
    "Γ",
    "γ",
--     "lunit",
    "Δ",
    "Γ",
    "γ",
--     "runit",
    "Ξ",
    "Θ",
    "Δ",
    "Γ",
    "ϑ",
    "δ",
    "γ",
--     "assoc",
    "empty",
    "Γ",
    "ε",
    "Γ",
    "f",
--     "ηε",
    "Ty",
    "Δ",
    "Γ",
    "substTy",
    "Γ",
    "A",
--     "idTy",
    "Θ",
    "Δ",
    "Γ",
    "A",
    "δ",
    "γ",
--     "compTy",
    "Γ",
    "Tm",
    "Δ",
    "Γ",
    "A",
    "γ",
    "substTm",
    "Γ",
    "A",
    "t",
--     "idTm",
    "Θ",
    "Δ",
    "Γ",
    "A",
    "t",
    "δ",
    "γ",
--     "compTm",
    "Γ",
    "ext",
    "Δ",
    "Γ",
    "A",
    "γ",
    "pair",
    "Θ",
    "Δ",
    "Γ",
    "A",
    "γ",
    "t",
    "δ",
--     "pair_nat",
    "Δ",
    "Γ",
    "A",
    "π₁",
    "Δ",
    "Γ",
    "A",
    "σ",
    "π₂",
    "Δ",
    "Γ",
    "A",
    "γ",
    "t",
--     "ext_β₁",
    "Δ",
    "Γ",
    "A",
    "γ",
    "t",
--     "ext_β₂",
    "Δ",
    "Γ",
    "A",
    "σ",
--     "ext_η"
]


-- #eval Con_toString ℭ𝔴𝔉
def Con_v : Nat → List String
| 0 => ["Γ"]
| 1 => "Δ" :: Con_v 0
| 2 => "Θ" :: Con_v 1
| 3 => "Ξ" :: Con_v 2
| _ => []

-- def twice (L : List String) := L ++ L
-- def CwF_record_names := ["Con","Sub","Γ","id"] ++ Con_v 2 ++ ["comp"] ++ twice (Con_v 1 ++ ["γ"] ) ++ Con_v 3 ++ ["ϑ","δ","γ","empty","Γ","ε","Γ","f",]
-- #eval CwF_names
-- #eval List.length CwF_topnames
-- #eval len ℭ𝔴𝔉
