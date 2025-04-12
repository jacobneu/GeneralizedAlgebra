import GeneralizedAlgebra.pretty_signatures.CwF

def ℭ𝔴𝔉₁ : GAT := ⦃
  include ℭ𝔴𝔉;
    unit : {Γ : Con} ⇒ Ty Γ,
    unit_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        substTy σ unit ≡ unit,
    star : {Γ : Con} ⇒ Tm Γ unit,
    star_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        substTm σ star   #⟨unit_stab σ⟩
        ≡ star,
    unit_elim : {Γ : Con} ⇒
        {M : Ty (ext Γ unit)} ⇒
        (m : Tm Γ (substTy (pair (id Γ) star) M)) ⇒
        Tm (ext Γ unit) M,
    unit_β : {Γ : Con} ⇒
        {M : Ty (ext Γ unit)} ⇒
        (m : Tm Γ (substTy (pair (id Γ) star) M)) ⇒
        substTm (pair (id Γ) star) (unit_elim m)
        ≡ m

⦄
