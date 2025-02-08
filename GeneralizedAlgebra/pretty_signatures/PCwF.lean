-- import GeneralizedAlgebra.signatures.CwF

def 𝔓ℭ𝔴𝔉 : GAT := ⦃
  include ℭ𝔴𝔉 as (Con, Sub,comp,id,_,_,_,empty,_,_, Ty,substTy,...);
    neg_Con    : Con ⇒ Con,
    neg_Sub    : ( Δ Γ : Con ) ⇒ Sub Δ Γ ⇒
        Sub (neg_Con Δ) (neg_Con Γ),
    neg_Ty     : ( Γ : Con ) ⇒ Ty Γ ⇒ Ty Γ,
    neg_empty  : neg_Con empty ≡ empty,
    neg_id     : ( Γ : Con ) ⇒
        neg_Sub (id Γ) ≡ id (neg_Con Γ),
    neg_comp   : ( Θ Δ Γ : Con ) ⇒
        (δ : Sub Θ Δ) ⇒ (γ : Sub Δ Γ) ⇒
        neg_Sub (comp γ δ)
        ≡ comp (neg_Sub γ) (neg_Sub δ),
    neg_nat    : ( Δ Γ : Con ) ⇒
        (γ : Sub Δ Γ) ⇒ (A : Ty Γ) ⇒
        neg_Ty Δ (substTy γ A)
        ≡ substTy γ (neg_Ty Γ A),
    invl_Con   : ( Γ : Con) ⇒ neg_Con(neg_Con Γ) ≡ Γ,
    invl_Sub   : ( Δ Γ : Con ) ⇒ (γ : Sub Δ Γ) ⇒
        neg_Sub(neg_Sub γ) ≡ γ,
    invl_Ty    : ( Γ : Con ) ⇒ (A : Ty Γ) ⇒
        neg_Ty (neg_Ty A) ≡ A
⦄
