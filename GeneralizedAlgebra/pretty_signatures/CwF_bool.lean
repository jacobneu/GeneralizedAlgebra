import GeneralizedAlgebra.pretty_signatures.CwF

def ℭ𝔴𝔉₁ : GAT := ⦃
  include ℭ𝔴𝔉;
    bool : {Γ : Con} ⇒ Ty Γ,
    bool_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        substTy σ bool ≡ bool,
    tt : {Γ : Con} ⇒ Tm Γ bool,
    tt_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        substTm σ tt   #⟨bool_stab σ⟩
        ≡ tt,
    ff : {Γ : Con} ⇒ Tm Γ bool,
    ff_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        substTm σ ff   #⟨bool_stab σ⟩
        ≡ ff,
    bool_elim : {Γ : Con} ⇒
        {M : Ty (ext Γ bool)} ⇒
        Tm Γ (substTy (pair (id Γ) tt) M) ⇒
        Tm Γ (substTy (pair (id Γ) ff) M) ⇒
        Tm (ext Γ bool) M,
    unit_β_tt : {Γ : Con} ⇒
        {M : Ty (ext Γ bool)} ⇒
        (mtt : Tm Γ (substTy (pair (id Γ) tt) M)) ⇒
        (mff : Tm Γ (substTy (pair (id Γ) ff) M)) ⇒
        substTm (pair (id Γ) tt) (bool_elim mtt mff)
        ≡ mtt,
    unit_β_ff : {Γ : Con} ⇒
        {M : Ty (ext Γ bool)} ⇒
        (mtt : Tm Γ (substTy (pair (id Γ) tt) M)) ⇒
        (mff : Tm Γ (substTy (pair (id Γ) ff) M)) ⇒
        substTm (pair (id Γ) ff) (bool_elim mtt mff)
        ≡ mff
⦄
