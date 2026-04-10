import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open psExp



def HomStr_Tm : List (Option (String × Bool)) → augTm → Option psExp
| topnames, augVAR n => (psDecorate · homFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f _ => HomStr_Tm topnames f
| topnames, augAPPi f _ => HomStr_Tm topnames f
| topnames, augTRANSP _ s => HomStr_Tm topnames s


def HomStr_Ty : List (Option (String × Bool)) → psExp → psExp → augTyMarker → StateT Nat Option psExp
| _, alg0, alg1, augUU => return psNopar [alg0,psLit "→",alg1]
| topnames, alg0, alg1, augEL X => do
    let sX ← HomStr_Tm topnames X
    return psNopar [psL [sX, alg0], psLit "=", alg1]
| topnames, alg0, alg1, augPI o X Y => do
    let strt ← (match o with
      | none => (·,true) <$> getName
      | _ => o)
    let aX0 ← AlgStr_Tm (List.map (Option.map (λ v => (zeroFn v.1,v.2))) topnames) X
    let hX ← HomStr_Tm topnames X
    let alg0' := if strt.2 then psL [alg0,psLit $ zeroFn strt.1] else alg0
    let alg1' := if strt.2 then psL [alg1,psR [hX,psLit $ zeroFn strt.1]] else alg1
    let hY ← HomStr_Ty (strt::topnames) alg0' alg1' Y
    return psDepI [(zeroFn strt.1,aX0)] hY
| _, _, _, augEQ _ _ => return psLit "⊤"


def HomStr_Con_core : List augTy → StateT Nat Option (List String)
| mkAugTy (some (s,true)) aT :: augCon => do
    let res ← HomStr_Con_core augCon
    let firstname ← HomStr_Ty (getTopnames augCon) (psLit $ zeroFn s) (psLit $ oneFn s) aT
    let finalStr ← OuterToString homFn (some (s,true)) firstname
    return res ++ [finalStr]
| [] => return []
| _ => none


def isntTrivial s := match List.reverse (String.toList s) with
| '⊤'::_ => false
| _ => true

def HomStrElim_outer : eliminator_outer augElim_inner := ⟨
    List String,
    λ Γ topnames telescopes => match
        (StateT.run (HomStr_Con_core (augCombine Γ topnames telescopes)) 0) with
        | some (ll,_) => List.filter isntTrivial ll
        | none => []
⟩
def HomStrElim := toEliminator HomStrElim_outer

syntax "[HomStr|" con_inner "]" : condata_outer
