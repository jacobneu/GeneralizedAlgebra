import GeneralizedAlgebra.signature

open Nat
open Ty Tm

-- mutual
--   def Con_toString : Con → String
--   | EMPTY => "⋄"
--   | Γ ▷ A => (Con_toString Γ) ++ " ▷ " ++ (Ty_toString A)
--   def Ty_toString : Ty → String
--   | UU => "U"
--   | EL X => "El " ++ paren (Tm_toString X)
--   | PI X UU => "Π " ++ paren (Tm_toString X) ++ " U"
--   | PI X Y => "Π " ++ paren (Tm_toString X) ++ " " ++ paren (Ty_toString Y)
--   | EQ t t' => "Eq " ++ paren (Tm_toString t) ++ " " ++ paren (Tm_toString t')
--   | SUBST_Ty σ T => (Ty_toString T) ++ " [ " ++ (Subst_toString σ) ++ " ]T"

--   def Tm_toString (theTerm : Tm) : String :=
--   match deBruijn theTerm with
--   | some n => Nat.repr n
--   | _ => match theTerm with
--     | (APP f) [ PAIR (ID _) t ]t => (Tm_toString f) ++ " @ " ++ paren (Tm_toString t)
--     | PROJ2 σ => "π₂ " ++ (Subst_toString σ)
--     | APP f => "App " ++ paren (Tm_toString f)
--     | t [ σ ]t => paren (Tm_toString t) ++ " [ " ++ (Subst_toString σ) ++ " ]t "
--   def Subst_toString : Subst → String
--   | PROJ1 (ID _) => "wk"
--   | PROJ1 σ => "π₁ " ++ (Subst_toString σ)
--   | PAIR σ t => (Subst_toString σ) ++ " , " ++ paren (Tm_toString t)
--   | EPSILON _ => "ε"
--   | COMP σ τ => (Subst_toString σ) ++ " ∘ " ++ (Subst_toString τ)
--   | (ID _) => "id"
-- end

def mkParen (s:String) : String :=
  if s.isNat then s else
  if s="U" then s else "("++s++")"

def wkStr (s : String) : String :=
match s.toNat? with
| (some n) => Nat.repr (succ n)
| _ => s ++ "[wk]"

instance ConStr_method : indData where
  Con_D := λ _ => String
  Ty_D := λ _ _ _ => String
  Tm_D := λ _ _ _ _ _ => String
  nil_D := "⋄"
  cons_D := λ _ 𝔊s _ As => 𝔊s ++ " ▷ " ++ As
  UU_D := λ _ _ => "U"
  EL_D := λ _ _ _ Xs => "El " ++ (mkParen Xs)
  PI_D := λ _ _ _ Xs _ Ys => "Π " ++ (mkParen Xs) ++ " " ++ (mkParen Ys)
  EQ_D := λ _ _ _ Xs _ ss _ ts => "Eq " ++ Xs ++ " " ++ ss ++ " " ++ ts
  VAR0_D := λ _ _ _ _ _ => "0"
  VARSUCC_D := λ _ _ _ _ _ ts _ _ _ => wkStr ts
  APP_D := λ _ _ _ _ _ _ _ fs _ xs _ => fs ++ " @ " ++ xs
  TRANSP_D := λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => "r"

instance GATRepr : Repr GAT :=
⟨ λ 𝔊 _ => 𝔊.elim ConStr_method ⟩
