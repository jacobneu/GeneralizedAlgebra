import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.formats.StringFormat

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp
open ArgMarker


def AlgStr_Tm : List ArgMarker → augTm → Option sfExp
| (Expl As)::_, augVAR 0 => return sfLit As
| (Impl As)::_, augVAR 0 => return sfLit As
| _::augCon, augVAR (succ n) => AlgStr_Tm augCon (augVAR n)
| topnames, augAPPx f t => do
    let sf ← AlgStr_Tm topnames f
    let st ← AlgStr_Tm topnames t
    return sfL [sf,st]
| topnames, augAPPi f _ => AlgStr_Tm topnames f
| augCon, augTRANSP _ s => AlgStr_Tm augCon s
| _,_ => none


def AlgStr_Ty : List ArgMarker → augTyMarker → Option sfExp
| tele, augPI o X Y => do
    let sX ← AlgStr_Tm tele X
    let sY ← AlgStr_Ty (o::tele) Y
    return sfDep  [(o,sX)] sY
| _, augUU => return sfLit "Set"
| tele, augEL X => AlgStr_Tm tele X
| tele, augEQ t1 t2 => do
    let s1 ← AlgStr_Tm tele t1
    let s2 ← AlgStr_Tm tele t2
    return sfNopar $ List.map sfExp.strictify [s1,sfLit "=",s2]

def getTopnames : List augTy → List ArgMarker :=
    List.map (λ (mkAugTy o _ ) => o)


def AlgStr_Con_core (SF : StringFormat) : List augTy → Option (List String)
| mkAugTy (Expl s) aT :: augCon => do
    let res ← AlgStr_Con_core SF augCon
    let firstname ← AlgStr_Ty (getTopnames augCon) aT
    let finalStr ← OuterToString SF id (some (s,true)) firstname
    return res ++ [finalStr]
| [] => return []
| _ => none

def AlgStr_Con (SF : StringFormat) : List augTy → List String := List.join ∘ Option.toList ∘ AlgStr_Con_core SF

def AlgStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (AlgStr_Con SF)

def AlgStrElim (SF : StringFormat) := toEliminator (AlgStrElim_outer SF)

syntax "[AlgStr|" con_inner "]" : condata_outer
