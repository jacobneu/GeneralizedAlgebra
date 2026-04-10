import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open psExp



def DAlgStr_Tm : List (Option (String × Bool))→ augTm → StateT Nat Option psExp
| topnames, augVAR n =>
    (psDecorate · dalgFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f s => do
    let sf ← DAlgStr_Tm topnames f
    let ss ← DAlgStr_Tm topnames s
    return psL [sf, ss]
| topnames, augAPPi f _ => DAlgStr_Tm topnames f
| topnames, augTRANSP _ s => DAlgStr_Tm topnames s

def DAlgArgFmt : (String × Bool) → psExp → psExp → psExp → psExp
| (s,true), aX, dX, psDep tele body =>
    psDepI [(s,aX)] $ psDep ((dalgFn s,psNopar [dX,psLit s])::tele) body
| (s,true), aX, dX, body =>
    psDepI [(s,aX)] $ psDep [(dalgFn s,psNopar [dX,psLit s])] body
| (s,false), aX, dX, psDepI tele body =>
    psDepI ((s,aX)::(dalgFn s,psNopar [dX,psLit s])::tele) body
| (s,false), aX, dX, body =>
    psDepI [(s,aX),(dalgFn s,psNopar [dX,psLit s])] body

def DAlgStr_Ty : List (Option (String × Bool)) → psExp → augTyMarker → StateT Nat Option psExp
| _, algS, augUU => return psNopar [algS,psLit " → ",psLit "Set"]
| topnames, algS, augEL X => (psL [ · , algS]) <$> DAlgStr_Tm topnames X
| topnames, _, augEQ t1 t2 => do
    let ps1 ← DAlgStr_Tm topnames t1
    let ps2 ← DAlgStr_Tm topnames t2
    return psNopar $ List.map psExp.strictify [ps1,psLit "=",ps2]
| topnames, algS, augPI o X Y => do
    let strt ← (match o with
      | none => (·,true) <$> getName
      | _ => o)
    let aX ← AlgStr_Tm topnames X
    let dX ← DAlgStr_Tm topnames X
    let algS' := if strt.2 then psNopar [algS,psLit strt.1] else algS
    let dY ← DAlgStr_Ty (strt::topnames) algS' Y
    return DAlgArgFmt strt aX dX dY


def DAlgStr_Con_core : List augTy → StateT Nat Option (List String)
| mkAugTy (some (s,true)) aT :: augCon => do
    let res ← DAlgStr_Con_core augCon
    let firstname ← DAlgStr_Ty (getTopnames augCon) (psLit s) aT
    let finalStr ← OuterToString dalgFn (some (s,true)) firstname
    return res ++ [finalStr]
| [] => return []
| _ => none

def DAlgStrElim_outer : eliminator_outer augElim_inner := ⟨
    List String,
    λ Γ topnames telescopes => match
        (StateT.run (DAlgStr_Con_core (augCombine Γ topnames telescopes)) 0) with
        | some (ll,_) => ll
        | none => []
⟩
def DAlgStrElim := toEliminator DAlgStrElim_outer

syntax "[DAlgStr|" con_inner "]" : condata_outer
