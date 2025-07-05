import GeneralizedAlgebra.signature
-- import Lean

-- open Lean Elab Meta
open Nat
open preTy preTm

mutual
inductive Con : Type where
| EMPTY : Con
| EXTEND : Con → Ty → Con

inductive Ty : Type where
| UU : Ty
| EL : Tm → Ty
| PI : Tm → Ty → Ty

inductive Tm : Type where
| VAR : Nat → Tm

end
open Con Ty Tm

#check congrFun

def Tm.decEq (t t' : Tm) : Decidable (Eq t t') :=
  match t, t' with
  | VAR m , VAR n => match Nat.decEq m n with
      | isTrue h => isTrue (congrArg VAR h)
      | isFalse h => isFalse (fun h' => by injection h' with e; exact h e)

def Ty.decEq (A B : Ty) : Decidable (Eq A B) :=
  match A, B with
  | UU , UU => isTrue rfl
  | UU , EL _ => isFalse (fun h => Ty.noConfusion h)
  | UU , PI _ _ => isFalse (fun h => Ty.noConfusion h)
  | EL _ , UU => isFalse (fun h => Ty.noConfusion h)
  | EL t , EL t' => match Tm.decEq t t' with
      | isTrue h => isTrue (congrArg EL h)
      | isFalse h => isFalse (fun h' => by injection h' with e; exact h e)
  | EL _ , PI _ _ => isFalse (fun h => Ty.noConfusion h)
  | PI _ _, UU => isFalse (fun h => Ty.noConfusion h)
  | PI _ _, EL _ => isFalse (fun h => Ty.noConfusion h)
  | PI X Y, PI X' Y' => match Tm.decEq X X', Ty.decEq Y Y' with
      | isTrue hX, isTrue hY => isTrue (congr (congrArg _ hX) hY)
      | isFalse hX, _ => isFalse (fun h' => by injection h' with e; exact hX e)
      | _ , isFalse hY => isFalse (fun h' => by injection h' with e e'; exact hY e')


instance : DecidableEq Ty := Ty.decEq

mutual
def compileCon : preCon → Option Con
| [] => some EMPTY
| A::AS => do
    let Γ ← compileCon AS
    let cA ← compileTy Γ A
    return EXTEND Γ cA

def compileTy : Con → preTy → Option Ty
| _ , preUU => some UU
| Γ , preEL X => do
    let cX ← compileTm Γ UU X
    return EL cX
| Γ , prePI X Y => do
    let cX ← compileTm Γ UU X
    let cY ← compileTy (EXTEND Γ (EL cX)) Y
    return PI cX cY
| _ , _ => none

def compileTm : Con → Ty → preTm → Option Tm
| EXTEND _ A, A' , preVAR 0 => if A=A' then some (VAR 0) else none
| EXTEND Γ _, A' , preVAR (succ n) =>
    (compileTm Γ A' (preVAR n)) >>= λ _ => some (VAR (succ n))
| _ , _ , _ => none

end

structure GAT extends GATdata where
  (typedCon : Option Con)
--   (elim : (P : indData) → P.Con_D con)

#reduce compileCon [preEL $ preVAR 1,preEL $ preVAR 0,preUU]
