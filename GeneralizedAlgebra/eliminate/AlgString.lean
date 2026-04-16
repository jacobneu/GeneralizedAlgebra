import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.formats.StringFormat

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp
open ArgMarker'


def AlgStr_Tm : List (ArgMarker' sfExp) → augTm → Option sfExp
| (Expl As)::_, augVAR 0 => return As
| (Impl As)::_, augVAR 0 => return As
| _::augCon, augVAR (succ n) => AlgStr_Tm augCon (augVAR n)
| topnames, augAPPx f t => do
    let sf ← AlgStr_Tm topnames f
    let st ← AlgStr_Tm topnames t
    return sfL [sf,st]
| topnames, augAPPi f _ => AlgStr_Tm topnames f
| augCon, augTRANSP _ s => AlgStr_Tm augCon s
| _,_ => none


def AlgStr_Ty : List (ArgMarker' sfExp) → augTyMarker → Option sfExp
| tele, augPI o X Y => do
    let sX ← AlgStr_Tm tele X
    let sY ← AlgStr_Ty (mkSfArgMark o::tele) Y
    return sfDep  [(mkSfArgMark o,sX)] sY
| _, augUU => return sfSet
| tele, augEL X => AlgStr_Tm tele X
| tele, augEQ t1 t2 => do
    let s1 ← AlgStr_Tm tele t1
    let s2 ← AlgStr_Tm tele t2
    return sfEq s1 s2

def getTopnames : List augTy → List (ArgMarker' sfExp) :=
    List.map (λ (mkAugTy o _ ) => mkSfArgMark o)

def Alg_Con_core : List augTy →  Option (List (String × sfExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← Alg_Con_core augCon
    let firstname ← AlgStr_Ty (getTopnames augCon) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


def AlgStr_Con (SF : StringFormat) (AΓ : List augTy) : List String :=
    match Alg_Con_core AΓ with
        | some ll =>  List.map (OuterToString SF sfDecor.sfId) ll
        | none => []

def AlgStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (AlgStr_Con SF)

def AlgStrElim (SF : StringFormat) := toEliminator (AlgStrElim_outer SF)

syntax "[AlgStr|" con_inner "]" : condata_outer
