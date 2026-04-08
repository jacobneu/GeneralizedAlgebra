import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm
open psExp



def DAlgStr_Tm : List String → augTm → psExp
| topnames, augVAR n => psDecorate (AlgStr_Tm topnames (augVAR n)) dalgFn
| topnames, augAPPx f s => psL [DAlgStr_Tm topnames f /-, AlgStr_Tm topnames s-/, DAlgStr_Tm topnames s]
| topnames, augAPPi f _ => DAlgStr_Tm topnames f --psL [DAlgStr_Tm topnames f, AlgStr_Tm topnames s, DAlgStr_Tm topnames s]
| topnames, augTRANSP _ s => DAlgStr_Tm topnames s


def DAlgStr_Ty : List String → List (Option (String × Bool)) → psExp → augTy → StateM Nat psExp
| _, _, algS, augUU => return psNopar [algS,psLit " → ",psLit "Set"]
| topnames, _, algS, augEL tt => return psL [DAlgStr_Tm topnames tt, algS]
| topnames, t::ts, algS, augPIx X Y => do
    let strt ← (match t with
      | none => getName
      | some (i,_) => return i)
    let resY ← DAlgStr_Ty (strt::topnames) ts (psNopar [algS,psLit strt]) Y
    match resY with
    | psDep tel body => return psDepI [(strt,AlgStr_Tm topnames X)] $ psDep ((dalgFn strt, psNopar [DAlgStr_Tm topnames X,psLit strt])::tel) body
    | body => return psDepI [(strt,AlgStr_Tm topnames X)] $ psDep [(dalgFn strt, psNopar [DAlgStr_Tm topnames X,psLit strt])] body
| topnames, t::ts, algS, augPIi X Y => do
    let strt ← (match t with
      | none => getName
      | some (i,_) => return i)
    let resY ← DAlgStr_Ty (strt::topnames) ts algS Y
    match resY with
    | psDepI tel body => return psDepI ((strt,AlgStr_Tm topnames X)::(dalgFn strt, psNopar [DAlgStr_Tm topnames X,psLit strt])::tel) body
    | body => return psDepI [(strt,AlgStr_Tm topnames X),(dalgFn strt, psNopar [DAlgStr_Tm topnames X,psLit strt])] body
| topnames, _, _, augEQ s t => return psNopar $ List.map psExp.strictify [DAlgStr_Tm topnames s,psLit "=",DAlgStr_Tm topnames t]
| _, _, _, _ => return psLit ""

def DAlgStr_Con_core : List String → List (augTy × List (Option (String × Bool))) → StateM Nat (List String)
| [], _ => do return []
| s::ss,(X,tt)::tts => do
    let restts ← DAlgStr_Con_core ss tts
    let resX ← DAlgStr_Ty ss tt (psLit s) X
    return restts ++ [collapseFor $ [dalgFn s, ":", psExp.toString resX ]]
| _,_ => return []

def DAlgStrElim_outer : eliminator_outer augElim_inner := ⟨
    List String,
    λ Γ topnames telescopes =>
        (StateT.run (DAlgStr_Con_core (List.reverse topnames) (List.zipWith GATdataZip_core Γ (List.reverse telescopes))) 0).1
⟩
def DAlgStrElim := toEliminator DAlgStrElim_outer

syntax "[DAlgStr|" con_inner "]" : condata_outer
