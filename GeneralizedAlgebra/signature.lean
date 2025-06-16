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
  | TRANSP : Tm → Tm → Tm
  | TRANSPop : Tm → Tm → Tm
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


-- namespace GAT

inductive Arg : Type where
| Impl : String → Ty → Arg
| Expl : String → Ty → Arg
| Anon : Ty → Arg
open Arg

def getName : Arg → Option String
| Impl i _ => some i
| Expl i _ => some i
| Anon _ => none

structure GAT where
  (con : Con)
  (topnames : List String)
  (telescopes : List (List Arg × Ty))

-- #check Listappend
def GAT.subnames (𝔊 : GAT) : List String :=
  List.join $
  List.map (λ (L,s) => L ++ [s]) $
  List.zip
    (List.map ((mappartial getName) ∘ Prod.fst) (GAT.telescopes 𝔊))
    (GAT.topnames 𝔊)

-- end GAT
