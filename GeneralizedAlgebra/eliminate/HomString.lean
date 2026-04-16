import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp
open ArgMarker



def HomStr_Tm (SF : StringFormat) : List ArgMarker → augTm → Option sfExp
| topnames, augVAR n => (sfDecorate · SF.homFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f _ => HomStr_Tm SF topnames f
| topnames, augAPPi f _ => HomStr_Tm SF topnames f
| topnames, augTRANSP _ s => HomStr_Tm SF topnames s


def HomStr_Ty (SF : StringFormat) : List ArgMarker → sfExp → sfExp → augTyMarker → StateT Nat Option sfExp
| _, alg0, alg1, augUU => return sfNopar [alg0,sfLit "→",alg1]
| topnames, alg0, alg1, augEL X => do
    let sX ← HomStr_Tm SF topnames X
    return sfNopar [sfL [sX, alg0], sfLit "=", alg1]
| topnames, alg0, alg1, augPI o X Y => do
    let varo ← getNameAM o
    let aX0 ← AlgStr_Tm (List.map (ArgMarker.map SF.zeroFn) topnames) X
    let hX ← HomStr_Tm SF topnames X
    let alg0' := if varo.2.2 then sfL [alg0,sfLit $ SF.zeroFn varo.2.1] else alg0
    let alg1' := if varo.2.2 then sfL [alg1,sfR [hX,sfLit $ SF.zeroFn varo.2.1]] else alg1
    let hY ← HomStr_Ty SF (varo.1::topnames) alg0' alg1' Y
    return sfDep [(Impl $ SF.zeroFn varo.2.1,aX0)] hY
| _, _, _, augEQ _ _ => return sfLit "⊤"


def Hom_Con_core (SF : StringFormat) : List augTy → StateT Nat Option (List (String × sfExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← Hom_Con_core SF augCon
    let firstname ← HomStr_Ty SF (getTopnames augCon) (sfLit $ SF.zeroFn s) (sfLit $ SF.oneFn s) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


def isntTrivial s := match List.reverse (String.toList s) with
| '⊤'::_ => false
| _ => true

def HomStr_Con (SF : StringFormat) (AΓ : List augTy) : List String :=
    match (StateT.run (Hom_Con_core SF AΓ) 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (λ (s,pe) => SF.collapseFor [SF.homFn s, ":", pe.toString]) ll
        | none => []

def HomStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (HomStr_Con SF)

def HomStrElim (SF : StringFormat) := toEliminator (HomStrElim_outer SF)

syntax "[HomStr|" con_inner "]" : condata_outer
