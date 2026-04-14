import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.HomString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open psExp
open ArgMarker



def SectStr_Tm : List ArgMarker → augTm → Option psExp
| topnames, augVAR n => (psDecorate · sectFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f _ => SectStr_Tm topnames f
| topnames, augAPPi f _ => SectStr_Tm topnames f
| topnames, augTRANSP _ s => SectStr_Tm topnames s


def SectStr_Ty : List ArgMarker → psExp → psExp → augTyMarker → StateT Nat Option psExp
| _, alg, dalg, augUU => do
    let v ← getName
    return psDep [(Expl v,alg)] $ psL [dalg,psLit v]
| topnames, alg, dalg, augEL X => do
    let sX ← SectStr_Tm topnames X
    return psNopar [psL [sX, alg], psLit "=", dalg]
| topnames, alg, dalg, augPI o X Y => do
    let varo ← getNameAM o
    let aX ← AlgStr_Tm topnames X
    let hX ← SectStr_Tm topnames X
    let alg' := if varo.2.2 then psL [alg,psLit varo.2.1] else alg
    let dalg' := if varo.2.2 then psL [dalg,psR [hX,psLit varo.2.1]] else dalg
    let hY ← SectStr_Ty (varo.1::topnames) alg' dalg' Y
    return psDep [(Impl $ varo.2.1,aX)] hY
| _, _, _, augEQ _ _ => return psLit "⊤"


def Sect_Con_core : List augTy → StateT Nat Option (List (String × psExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← Sect_Con_core augCon
    let firstname ← SectStr_Ty (getTopnames augCon) (psLit s) (psLit $ dalgFn s) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


-- def isntTrivial s := match List.reverse (String.toList s) with
-- | '⊤'::_ => false
-- | _ => true

def SectStr_Con (AΓ : List augTy) : List String :=
    match (StateT.run (Sect_Con_core AΓ) 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (λ (s,pe) => collapseFor [sectFn s, ":", pe.toString]) ll
        | none => []

def SectStrElim_outer : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer SectStr_Con

def SectStrElim := toEliminator SectStrElim_outer

syntax "[SectStr|" con_inner "]" : condata_outer
