import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.HomString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp
open ArgMarker



def SectStr_Tm (SF : StringFormat) : List ArgMarker → augTm → Option sfExp
| topnames, augVAR n => (sfDecorate · SF.sectFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f _ => SectStr_Tm SF topnames f
| topnames, augAPPi f _ => SectStr_Tm SF topnames f
| topnames, augTRANSP _ s => SectStr_Tm SF topnames s


def SectStr_Ty (SF : StringFormat) : List ArgMarker → sfExp → sfExp → augTyMarker → StateT Nat Option sfExp
| _, alg, dalg, augUU => do
    let v ← getName
    return sfDep [(Expl v,alg)] $ sfL [dalg,sfLit v]
| topnames, alg, dalg, augEL X => do
    let sX ← SectStr_Tm SF topnames X
    return sfNopar [sfL [sX, alg], sfLit "=", dalg]
| topnames, alg, dalg, augPI o X Y => do
    let varo ← getNameAM o
    let aX ← AlgStr_Tm topnames X
    let hX ← SectStr_Tm SF topnames X
    let alg' := if varo.2.2 then sfL [alg,sfLit varo.2.1] else alg
    let dalg' := if varo.2.2 then sfL [dalg,sfR [hX,sfLit varo.2.1]] else dalg
    let hY ← SectStr_Ty SF (varo.1::topnames) alg' dalg' Y
    return sfDep [(Impl $ varo.2.1,aX)] hY
| _, _, _, augEQ _ _ => return sfLit "⊤"


def Sect_Con_core (SF : StringFormat) : List augTy → StateT Nat Option (List (String × sfExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← Sect_Con_core SF augCon
    let firstname ← SectStr_Ty SF (getTopnames augCon) (sfLit s) (sfLit $ SF.dalgFn s) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


-- def isntTrivial s := match List.reverse (String.toList s) with
-- | '⊤'::_ => false
-- | _ => true

def SectStr_Con (SF : StringFormat) (AΓ : List augTy) : List String :=
    match (StateT.run (Sect_Con_core SF AΓ) 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (λ (s,pe) => SF.collapseFor [SF.sectFn s, ":", pe.toString]) ll
        | none => []

def SectStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (SectStr_Con SF)

def SectStrElim (SF : StringFormat) := toEliminator (SectStrElim_outer SF)

syntax "[SectStr|" con_inner "]" : condata_outer
