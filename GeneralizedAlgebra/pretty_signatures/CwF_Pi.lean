import GeneralizedAlgebra.pretty_signatures.CwF

def ℭ𝔴𝔉pi : GAT := ⦃
  include ℭ𝔴𝔉;
    Pi : {Γ : Con} ⇒
        (A : Ty Γ) ⇒ Ty (ext Γ A) ⇒ Ty Γ,
    Pi_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        (A : Ty Γ) ⇒ (B : Ty (ext Γ A)) ⇒
        substTy Δ Γ σ (Pi A B)
        ≡ Pi (substTy σ A)
             (substTy (pair
                    (comp σ (p (substTy σ A)))
                    (v (substTy σ A)))
             B),
    lam : {Γ : Con} ⇒
        {A : Ty Γ} ⇒ {B : Ty (ext Γ A)} ⇒
        Tm (ext Γ A) B ⇒ Tm Γ (Pi A B),
    app : {Γ : Con} ⇒
        {A : Ty Γ} ⇒ {B : Ty (ext Γ A)} ⇒
        Tm Γ (Pi A B) ⇒ Tm (ext Γ A) B,
    lam_stab : {Δ Γ : Con} ⇒ (σ : Sub Δ Γ) ⇒
        {A : Ty Γ} ⇒ {B : Ty (ext Γ A)} ⇒
        (t : Tm (ext Γ A) B) ⇒
        substTm σ (Pi A B) (lam t)
            #⟨Pi_stab σ A B⟩
        ≡ (lam (substTm
                    (pair (comp σ (p (substTy σ A)))
                    (v (substTy σ A)))
                t)
          ),
    Pi_β : {Γ : Con} ⇒
        {A : Ty Γ} ⇒ {B : Ty (ext Γ A)} ⇒
        (t : Tm (ext Γ A) B) ⇒ app (lam t) ≡ t,
    Pi_η : {Γ : Con} ⇒
        {A : Ty Γ} ⇒ {B : Ty (ext Γ A)} ⇒
        (f : Tm Γ (Pi A B)) ⇒ lam (app f) ≡ f
⦄
