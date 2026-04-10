import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.formats.PseudoAgda

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open psExp


def AlgStr_Tm : List (Option (String × Bool)) → augTm → Option psExp
| (some (As,_))::_, augVAR 0 => return psLit As
| _::augCon, augVAR (succ n) => AlgStr_Tm augCon (augVAR n)
| topnames, augAPPx f t => do
    let sf ← AlgStr_Tm topnames f
    let st ← AlgStr_Tm topnames t
    return psL [sf,st]
| topnames, augAPPi f _ => AlgStr_Tm topnames f
| augCon, augTRANSP _ s => AlgStr_Tm augCon s
| _,_ => none

def AlgArgFmt : Option (String × Bool) → psExp → psExp → psExp
| none, sX, sY =>
    psNopar [sX, psLit "→", sY]
| some (s,true), sX, psDep tele body =>
    psDep ((s,sX)::tele) body
| some (s,true), sX, sY =>
    psDep [(s,sX)] sY
| some (s,false), sX, psDepI tele body =>
    psDepI ((s,sX)::tele) body
| some (s,false), sX, sY =>
    psDepI [(s,sX)] sY

def AlgStr_Ty : List (Option (String × Bool)) → augTyMarker → Option psExp
| tele, augPI o X Y => do
    let sX ← AlgStr_Tm tele X
    let sY ← AlgStr_Ty (o::tele) Y
    return AlgArgFmt o sX sY
| _, augUU => return psLit "Set"
| tele, augEL X => AlgStr_Tm tele X
| tele, augEQ t1 t2 => do
    let s1 ← AlgStr_Tm tele t1
    let s2 ← AlgStr_Tm tele t2
    return psNopar $ List.map psExp.strictify [s1,psLit "=",s2]

def getTopnames : List augTy → List (Option (String × Bool)) :=
    List.map (λ (mkAugTy o _ ) => o)


def AlgStr_Con_core : List augTy → Option (List String)
| mkAugTy (some (s,true)) aT :: augCon => do
    let res ← AlgStr_Con_core augCon
    let firstname ← AlgStr_Ty (getTopnames augCon) aT
    let finalStr ← OuterToString id (some (s,true)) firstname
    return res ++ [finalStr]
| [] => return []
| _ => none


def AlgStrElim_outer : eliminator_outer augElim_inner := ⟨
    List String,
    λ Γ topnames telescopes => match AlgStr_Con_core (augCombine Γ topnames telescopes) with
        | some l => l
        | none => []
⟩
def AlgStrElim := toEliminator AlgStrElim_outer

syntax "[AlgStr|" con_inner "]" : condata_outer
