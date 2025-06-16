import GeneralizedAlgebra.signature

open Nat
open Ty Tm

instance AlgStr : indData where
  Con_D := λ _ => String
  Ty_D := λ _ _ _ => String
  Tm_D := λ _ _ _ _ _ => String
  nil_D := "⋄"
  cons_D := λ 𝔊 𝔊s A As => 𝔊s ++ " × " ++ As
  UU_D := λ _ _ => "Set"
  EL_D := λ _ 𝔊s _ Xs => 𝔊s ++ "-" ++ Xs
  PI_D := λ _ _ _ _ _ _ => "w"
  EQ_D := λ _ _ _ _ _ _ _ _ => "v"
  VAR0_D := λ _ 𝔊s _ As A's => "(" ++ As ++ "|" ++ A's ++ ")"
  VARSUCC_D := λ _ _ _ _ _ _ _ _ _ => "t"
  APP_D := λ _ _ _ _ _ _ _ _ _ _ _ => "s"
  TRANSP_D := λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => "r"

instance Alg : indData where
  Con_D := λ _ => Type 1
  Ty_D := λ _ Γ _ => Γ → Type 1
  Tm_D := λ _ Γ _ A _ => (γ : Γ) → A γ
  nil_D := PUnit
  cons_D := λ 𝔊 Γ _ A => Sigma (λ γ => A γ)
  UU_D := λ _ _ _ => Type
  EL_D := λ _ 𝔊s _ Xs γ => Xs γ
  -- PI_D := λ _ _ _ _ _ _ => "w"
  -- EQ_D := λ _ _ _ _ _ _ _ _ => "v"
  -- VAR0_D := λ _ 𝔊s _ As A's => "(" ++ As ++ "|" ++ A's ++ ")"
  -- VARSUCC_D := λ _ _ _ _ _ _ _ _ _ => "t"
  -- APP_D := λ _ _ _ _ _ _ _ _ _ _ _ => "s"
  -- TRANSP_D := λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => "r"
