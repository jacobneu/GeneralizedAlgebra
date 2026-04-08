import GeneralizedAlgebra.eliminate.DAlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm
open psExp


def homFor sl := (parenFor sl) ++ "ᴹ"
def homFn s := s ++ "ᴹ"
def zeroFn s := s ++ "₀"
def oneFn s := s ++ "₁"


def HomStr_Tm : List String → augTm → psExp
| topnames, augVAR n => psDecorate (AlgStr_Tm topnames (augVAR n)) homFn
| topnames, augAPPx f _ => HomStr_Tm topnames f/-, psDecorate (AlgStr_Tm topnames s) zeroFn-/
| topnames, augAPPi f _ => HomStr_Tm topnames f/-, psDecorate (AlgStr_Tm topnames s) zeroFn-/
-- | topnames, augAPPi f _ => HomStr_Tm topnames f --psL [HomStr_Tm topnames f, AlgStr_Tm topnames s, HomStr_Tm topnames s]
| topnames, augTRANSP _ s => HomStr_Tm topnames s


def HomStr_Ty : List String → List (Option (String × Bool)) → psExp → psExp → augTy → StateM Nat psExp
| _, _, alg0, alg1, augUU => return psNopar [alg0,psLit "→",alg1]
| topnames, _, alg0, alg1, augEL tt => return psNopar [psL [HomStr_Tm topnames tt, alg0], psLit "=", alg1]
| topnames, t::ts, alg0, alg1, augPIx X Y => do
    let strt ← (match t with
      | none => getName
      | some (i,_) => return i)
    let resY ← HomStr_Ty (strt::topnames) ts (psL [alg0,psLit $ zeroFn strt]) (psL [alg1,psR [HomStr_Tm topnames X,psLit $ zeroFn strt]]) Y
    return psDepI [(zeroFn strt,AlgStr_Tm (List.map zeroFn topnames) X)] resY
| topnames, t::ts, alg0, alg1, augPIi X Y => do
    let strt ← (match t with
      | none => getName
      | some (i,_) => return i)
    let resY ← HomStr_Ty (strt::topnames) ts alg0 alg1 Y
    return psDepI [(zeroFn strt,AlgStr_Tm (List.map zeroFn topnames) X)] resY
| _, _, _, _, augEQ _ _ => return psLit "⊤"
| _, _, _, _, _ => return psLit ""

def HomStr_Con_core : List String → List (augTy × List (Option (String × Bool))) → StateM Nat (List String)
| s::ss,(X,tt)::tts => do
    let restts ← HomStr_Con_core ss tts
    let resX ← HomStr_Ty ss tt (psLit $ zeroFn s) (psLit $ oneFn s) X
    return restts ++ [collapseFor $ [homFn s, ":", psExp.toString resX ]]
| _,_ => return []

def isntTrivial s := match List.reverse (String.toList s) with
| '⊤'::_ => false
| _ => true

def HomStrElim_outer : eliminator_outer augElim_inner := ⟨
    List String,
    λ Γ topnames telescopes =>
        List.filter isntTrivial
        (StateT.run (HomStr_Con_core (List.reverse topnames) (List.zipWith GATdataZip_core Γ (List.reverse telescopes))) 0).1
⟩
def HomStrElim := toEliminator HomStrElim_outer


syntax "[HomStr|" "]" : condata_outer
syntax "[HomStr|" con_inner "]" : condata_outer
