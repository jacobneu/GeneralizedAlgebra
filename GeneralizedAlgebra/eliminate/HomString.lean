import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp sfDecor
open ArgMarker'



def HomStr_Tm : List (ArgMarker' sfExp) → augTm → Option sfExp
| topnames, augVAR n =>  do
    let iarg ← topnames[n]?
    match iarg with
    | Expl i => return sfDec i sfHom
    | Impl i => return sfDec i sfHom --shouldn't happen
    | Anon => none  --shouldn't happen
| topnames, augAPPx f _ => HomStr_Tm topnames f
| topnames, augAPPi f _ => HomStr_Tm topnames f
| topnames, augTRANSP _ s => HomStr_Tm topnames s


def HomStr_Ty : List (ArgMarker' sfExp) → sfExp → sfExp → augTyMarker → StateT Nat Option sfExp
| _, alg0, alg1, augUU => return sfArr alg0 alg1
| topnames, alg0, alg1, augEL X => do
    let sX ← HomStr_Tm topnames X
    return sfEq (sfL [sX, alg0]) alg1
| topnames, alg0, alg1, augPI o X Y => do
    let varo ← getNameAM o
    let aX0 ← AlgStr_Tm (List.map (argDec sfZero) topnames) X
    let hX ← HomStr_Tm topnames X
    let alg0' := if varo.2.2 then sfL [alg0,sfIdentDec varo.2.1 sfZero] else alg0
    let alg1' := if varo.2.2 then sfL [alg1,sfR [hX,sfIdentDec varo.2.1 sfZero]] else alg1
    let hY ← HomStr_Ty (varo.1::topnames) alg0' alg1' Y
    return sfDep [(Impl (sfIdentDec varo.2.1 sfZero),aX0)] hY
| _, _, _, augEQ _ _ => return sfTop


def Hom_Con_core : List augTy → StateT Nat Option (List (String × sfExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← Hom_Con_core augCon
    let firstname ← HomStr_Ty (getTopnames augCon) (sfIdentDec s sfZero) (sfIdentDec s sfOne) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


def isntTrivial s := match List.reverse (String.toList s) with
| '⊤'::_ => false
| _ => true

def HomStr_Con (SF : StringFormat) (AΓ : List augTy) : List String :=
    match (StateT.run (Hom_Con_core AΓ) 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (OuterToString SF sfHom) ll
        | none => []

def HomStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (HomStr_Con SF)

def HomStrElim (SF : StringFormat) := toEliminator (HomStrElim_outer SF)

syntax "[HomStr|" con_inner "]" : condata_outer
