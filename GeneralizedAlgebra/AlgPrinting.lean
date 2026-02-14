import GeneralizedAlgebra.typecheck

open Nat
open preTy preTm
open wellCon


mutual
def AlgCon0 : Type 1 := PUnit
end

mutual

def AlgTy1 : ∀ (A : preTy), wellTy [] A → AlgCon0 → Type 1
| preUU, _, _ => Type
| _, _, _ => Type

def AlgCon1 : ∀ (A : preTy), wellTy [] A → Type 1
| A, wA => AlgTy1 A wA PUnit.unit

end

mutual

def AlgTy2 : ∀ (Γ₀ : preTy) (wΓ₀ : wellTy [] Γ₀) (A : preTy), wellTy [Γ₀] A → AlgCon1 Γ₀ wΓ₀ → Type 1
| _, _, _, _, _ => Type

def AlgCon2 : ∀ (Γ₀ : preTy) (_ : wellTy [] Γ₀) (A : preTy), wellTy [Γ₀] A → Type 1
| Γ₀, wΓ₀, A, wA => Sigma (AlgTy2 Γ₀ wΓ₀ A wA)

end

mutual
def AlgTy3 : ∀ (Γ₀ Γ₁: preTy) (wΓ₀ : wellTy [] Γ₀) (wΓ₁ : wellTy [Γ₀] Γ₁) (A : preTy), wellTy [Γ₁,Γ₀] A → AlgCon2 Γ₀ wΓ₀ Γ₁ wΓ₁ → Type 1
| _, _, _, _, _, _,_ => Type

def AlgCon3 : ∀ (Γ₀ Γ₁: preTy) (_: wellTy [] Γ₀) (_: wellTy [Γ₀] Γ₁) (A : preTy), wellTy [Γ₁,Γ₀] A → Type 1
| Γ₀, Γ₁, wΓ₀, wΓ₁, A, wA => Sigma (AlgTy3 Γ₀ Γ₁ wΓ₀ wΓ₁ A wA)

end





def Alg : ∀ (Γ : preCon), wellCon Γ → Type 1
| [], _ => AlgCon0
| [Γ₀], wellCons wΓ₀ wellEmpty => AlgCon1 Γ₀ wΓ₀
| [Γ₁,Γ₀], wellCons wΓ₁ (wellCons wΓ₀ wellEmpty) => AlgCon2 Γ₀ wΓ₀ Γ₁ wΓ₁
| [Γ₂,Γ₁,Γ₀], wellCons wΓ₂ (wellCons wΓ₁ (wellCons wΓ₀ wellEmpty)) => AlgCon3 Γ₀ Γ₁ wΓ₀ wΓ₁ Γ₂ wΓ₂
| _,_ => PUnit
-- instance AlgStr_method : indData where
--   Con_D := λ _ => String
--   Ty_D := λ _ _ _ => String
--   Tm_D := λ _ _ _ _ _ => String
--   nil_D := "⋄"
--   cons_D := λ 𝔊 𝔊s A As => 𝔊s ++ " × " ++ As
--   UU_D := λ _ _ => "Set"
--   EL_D := λ _ 𝔊s _ Xs => 𝔊s ++ "-" ++ Xs
--   PI_D := λ _ _ _ _ _ _ => "w"
--   EQ_D := λ _ _ _ _ _ _ _ _ => "v"
--   VAR0_D := λ _ 𝔊s _ As A's => "(" ++ As ++ "|" ++ A's ++ ")"
--   VARSUCC_D := λ _ _ _ _ _ _ _ _ _ => "t"
--   APP_D := λ _ _ _ _ _ _ _ _ _ _ _ => "s"
--   TRANSP_D := λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => "r"

-- instance Alg : indData where
--   Con_D := λ _ => Type 1
--   Ty_D := λ _ Γ _ => Γ → Type 1
--   Tm_D := λ _ Γ _ A _ => (γ : Γ) → A γ
--   nil_D := PUnit
--   cons_D := λ 𝔊 Γ _ A => Sigma (λ γ => A γ)
--   UU_D := λ _ _ _ => Type
--   EL_D := λ _ 𝔊s _ Xs γ => Xs γ
  -- PI_D := λ _ _ _ _ _ _ => "w"
  -- EQ_D := λ _ _ _ _ _ _ _ _ => "v"
  -- VAR0_D := λ _ 𝔊s _ As A's => "(" ++ As ++ "|" ++ A's ++ ")"
  -- VARSUCC_D := λ _ _ _ _ _ _ _ _ _ => "t"
  -- APP_D := λ _ _ _ _ _ _ _ _ _ _ _ => "s"
  -- TRANSP_D := λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => "r"
