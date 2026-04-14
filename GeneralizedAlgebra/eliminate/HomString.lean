import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open psExp
open ArgMarker



def HomStr_Tm : List ArgMarker → augTm → Option psExp
| topnames, augVAR n => (psDecorate · homFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f _ => HomStr_Tm topnames f
| topnames, augAPPi f _ => HomStr_Tm topnames f
| topnames, augTRANSP _ s => HomStr_Tm topnames s


def HomStr_Ty : List ArgMarker → psExp → psExp → augTyMarker → StateT Nat Option psExp
| _, alg0, alg1, augUU => return psNopar [alg0,psLit "→",alg1]
| topnames, alg0, alg1, augEL X => do
    let sX ← HomStr_Tm topnames X
    return psNopar [psL [sX, alg0], psLit "=", alg1]
| topnames, alg0, alg1, augPI o X Y => do
    let varo ← getNameAM o
    let aX0 ← AlgStr_Tm (List.map (ArgMarker.map zeroFn) topnames) X
    let hX ← HomStr_Tm topnames X
    let alg0' := if varo.2.2 then psL [alg0,psLit $ zeroFn varo.2.1] else alg0
    let alg1' := if varo.2.2 then psL [alg1,psR [hX,psLit $ zeroFn varo.2.1]] else alg1
    let hY ← HomStr_Ty (varo.1::topnames) alg0' alg1' Y
    return psDep [(Impl $ zeroFn varo.2.1,aX0)] hY
| _, _, _, augEQ _ _ => return psLit "⊤"


def Hom_Con_core : List augTy → StateT Nat Option (List (String × psExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← Hom_Con_core augCon
    let firstname ← HomStr_Ty (getTopnames augCon) (psLit $ zeroFn s) (psLit $ oneFn s) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


def isntTrivial s := match List.reverse (String.toList s) with
| '⊤'::_ => false
| _ => true

def HomStr_Con (AΓ : List augTy) : List String :=
    match (StateT.run (Hom_Con_core AΓ) 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (λ (s,pe) => collapseFor [homFn s, ":", pe.toString]) ll
        | none => []

def HomStrElim_outer : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer HomStr_Con

def HomStrElim := toEliminator HomStrElim_outer

syntax "[HomStr|" con_inner "]" : condata_outer
