import GeneralizedAlgebra.signature

open Nat
open Con Subst Ty Tm

mutual
  def Con_toString : Con → String
  | EMPTY => "⋄"
  | Γ ▷ A => (Con_toString Γ) ++ s!"{NEWLINE}▷ " ++ (Ty_toString A)
  def Ty_toString : Ty → String
  | UU => "U"
  | EL X => "El " ++ paren (Tm_toString X)
  | PI X UU => "Π " ++ paren (Tm_toString X) ++ " U"
  | PI X Y => "Π " ++ paren (Tm_toString X) ++ " " ++ paren (Ty_toString Y)
  | EQ t t' => "Eq " ++ paren (Tm_toString t) ++ " " ++ paren (Tm_toString t')
  | SUBST_Ty σ T => (Ty_toString T) ++ " [ " ++ (Subst_toString σ) ++ " ]T"

  def Tm_toString (theTerm : Tm) : String :=
  match deBruijn theTerm with
  | some n => Nat.repr n
  | _ => match theTerm with
    | (APP f) [ PAIR (ID _) t ]t => (Tm_toString f) ++ " @ " ++ paren (Tm_toString t)
    | PROJ2 σ => "π₂ " ++ (Subst_toString σ)
    | APP f => "App " ++ paren (Tm_toString f)
    | t [ σ ]t => paren (Tm_toString t) ++ " [ " ++ (Subst_toString σ) ++ " ]t "
    | (TRANSP t e) => "transp (" ++ (Tm_toString e) ++ ") (" ++ (Tm_toString t) ++ ")"
    | (TRANSPop t e) => "transp⁻¹ (" ++ (Tm_toString e) ++ ") (" ++ (Tm_toString t) ++ ")"
  def Subst_toString : Subst → String
  | PROJ1 (ID _) => "wk"
  | PROJ1 σ => "π₁ " ++ (Subst_toString σ)
  | PAIR σ t => (Subst_toString σ) ++ " , " ++ paren (Tm_toString t)
  | EPSILON _ => "ε"
  | COMP σ τ => (Subst_toString σ) ++ " ∘ " ++ (Subst_toString τ)
  | (ID _) => "id"
end

instance GATRepr : Repr GAT :=
⟨ λ 𝔊 _ => Con_toString 𝔊.con⟩
