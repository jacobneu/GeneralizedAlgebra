import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.HomString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp sfDecor
open ArgMarker'



def SectStr_Tm : List (Option sfExp) → augTm → Option sfExp
| topnames, augVAR n => (sfDec · sfSect) <$> Option.join topnames[n]?
| topnames, augAPPx f _ => SectStr_Tm topnames f
| topnames, augAPPi f _ => SectStr_Tm topnames f
| topnames, augTRANSP _ s => SectStr_Tm topnames s


def SectStr_Ty : List (Option sfExp) → sfExp → sfExp → augTyMarker → StateT Nat Option sfExp
| _, alg, dalg, augUU => do
    let v ← getName
    return sfDep [(Expl $ sfIdent v,alg)] $ sfL [dalg,sfIdent v]
| topnames, alg, dalg, augEL X => do
    let sX ← SectStr_Tm topnames X
    return sfEq (sfL [sX, alg]) dalg
| topnames, alg, dalg, augPI o X Y => do
    let varo ← getNameAM o
    let aX ← AlgStr_Tm topnames X
    let hX ← SectStr_Tm topnames X
    let alg' := if varo.2.2 then sfL [alg,sfIdent varo.2.1] else alg
    let dalg' := if varo.2.2 then sfL [dalg,sfR [hX,sfIdent varo.2.1]] else dalg
    let hY ← SectStr_Ty (sfIdent varo.2.1::topnames) alg' dalg' Y
    return sfDep [(Impl $ sfIdent varo.2.1,aX)] hY
| _, _, _, augEQ _ _ => return sfTop


def Sect_Con_core : List (Option String × augTyMarker) → StateT Nat Option (List (String × sfExp))
| (os,aT) :: augCon => do
    let s ← os
    let res ← Sect_Con_core augCon
    let firstname ← SectStr_Ty (augCon.map (λ (os',_) => sfIdent <$> os')) (sfIdent s) (sfIdentDec s sfDalg) aT
    return res ++ [(s,firstname)]
| [] => return []


-- def isntTrivial s := match List.reverse (String.toList s) with
-- | '⊤'::_ => false
-- | _ => true

def SectStr_Con (SF : StringFormat) (AΓ : List augTy) (algNames : List String := []): List String :=
    let AΓ' := (List.zipWithSnd (λ os (mkAugTy as aT) => Option.elim os (extractIdent? as,aT) (some ·,aT)) algNames AΓ.reverse).reverse
    match (StateT.run (Sect_Con_core AΓ') 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (OuterToString SF sfSect) ll
        | none => []

def SectStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (SectStr_Con SF)

def SectStrElim (SF : StringFormat) := toEliminator (SectStrElim_outer SF)

syntax "[SectStr|" con_inner "]" : condata_outer
