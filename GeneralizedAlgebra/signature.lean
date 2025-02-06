import GeneralizedAlgebra.helper


open Nat

mutual
  inductive Con : Type where
  | EMPTY : Con
  | EXTEND : Con → Ty → Con

  inductive Subst : Type where
  | EPSILON : Con → Subst
  | ID : Con → Subst
  | COMP : Subst → Subst → Subst
  | PAIR : Subst → Tm → Subst
  | PROJ1 : Subst → Subst

  inductive Ty : Type where
  | SUBST_Ty : Subst → Ty → Ty
  | UU : Ty
  | EL : Tm → Ty
  | PI : Tm → Ty → Ty
  | EQ : Tm → Tm → Ty

  inductive Tm : Type where
  | SUBST_Tm : Subst → Tm → Tm
  | PROJ2 : Subst → Tm
  | APP : Tm → Tm
end

open Con Subst Ty Tm


infixl:10 " ▷ " => EXTEND
notation t " [ " σ " ]t " => SUBST_Tm σ t

def len : Con → Nat
| EMPTY => 0
| Γ ▷ _ => succ (len Γ)

def deBruijn : Tm → Option Nat
| PROJ2 (ID _) => some 0
| t [ PROJ1 (ID _) ]t => do let res ← deBruijn t; return (succ res)
| _ => none

def wk (Γ : Con) (A : Ty) : Subst := PROJ1 (@ID (Γ ▷ A))
def V0 (Γ : Con) (T0 : Ty) : Tm := PROJ2 (@ID (Γ ▷ T0))

def GAT : Type := Con
