import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open psExp
open ArgMarker



def DAlgStr_Tm : List ArgMarker → augTm → StateT Nat Option psExp
| topnames, augVAR n =>
    (psDecorate · dalgFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f s => do
    let sf ← DAlgStr_Tm topnames f
    let ss ← DAlgStr_Tm topnames s
    return psL [sf, ss]
| topnames, augAPPi f _ => DAlgStr_Tm topnames f
| topnames, augTRANSP _ s => DAlgStr_Tm topnames s

def DAlgArgFmt : ArgMarker → psExp → psExp → psExp → Option psExp
| Expl s, aX, dX, body =>
    psDep [(Impl s,aX)] $ psDep [(Expl $ dalgFn s,psNopar [dX,psLit s])] body
| Impl s, aX, dX, body =>
    psDep [(Impl s,aX),(Impl $ dalgFn s,psNopar [dX,psLit s])] body
| _, _, _, _ => none

def DAlgStr_Ty : List ArgMarker → psExp → augTyMarker → StateT Nat Option psExp
| _, algS, augUU => return psNopar [algS,psLit " → ",psLit "Set"]
| topnames, algS, augEL X => (psL [ · , algS]) <$> DAlgStr_Tm topnames X
| topnames, _, augEQ t1 t2 => do
    let ps1 ← DAlgStr_Tm topnames t1
    let ps2 ← DAlgStr_Tm topnames t2
    return psNopar $ List.map psExp.strictify [ps1,psLit "=",ps2]
| topnames, algS, augPI o X Y => do
    let varo ← getNameAM o
    let aX ← AlgStr_Tm topnames X
    let dX ← DAlgStr_Tm topnames X
    let algS' := if varo.2.2 then psNopar [algS,psLit varo.2.1] else algS
    let dY ← DAlgStr_Ty (varo.1::topnames) algS' Y
    DAlgArgFmt varo.1 aX dX dY


def DAlgStr_Con_core : List augTy → StateT Nat Option (List String)
| mkAugTy (Expl s) aT :: augCon => do
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
