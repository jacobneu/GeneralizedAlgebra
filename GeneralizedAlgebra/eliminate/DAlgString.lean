import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp
open ArgMarker



def DAlgStr_Tm (SF : StringFormat) : List ArgMarker → augTm → StateT Nat Option sfExp
| topnames, augVAR n =>
    (sfDecorate · SF.dalgFn) <$> AlgStr_Tm topnames (augVAR n)
| topnames, augAPPx f s => do
    let sf ← DAlgStr_Tm SF topnames f
    let ss ← DAlgStr_Tm SF topnames s
    return sfL [sf, ss]
| topnames, augAPPi f _ => DAlgStr_Tm SF topnames f
| topnames, augTRANSP _ s => DAlgStr_Tm SF topnames s

def DAlgArgFmt (SF : StringFormat) : ArgMarker → sfExp → sfExp → sfExp → Option sfExp
| Expl s, aX, dX, body =>
    sfDep [(Impl s,aX)] $ sfDep [(Expl $ SF.dalgFn s,sfNopar [dX,sfLit s])] body
| Impl s, aX, dX, body =>
    sfDep [(Impl s,aX),(Impl $ SF.dalgFn s,sfNopar [dX,sfLit s])] body
| _, _, _, _ => none

def DAlgStr_Ty (SF : StringFormat) : List ArgMarker → sfExp → augTyMarker → StateT Nat Option sfExp
| _, algS, augUU => return sfNopar [algS,sfLit " → ",sfLit "Set"]
| topnames, algS, augEL X => (sfL [ · , algS]) <$> DAlgStr_Tm SF topnames X
| topnames, _, augEQ t1 t2 => do
    let sf1 ← DAlgStr_Tm SF topnames t1
    let sf2 ← DAlgStr_Tm SF topnames t2
    return sfNopar $ List.map sfExp.strictify [sf1,sfLit "=",sf2]
| topnames, algS, augPI o X Y => do
    let varo ← getNameAM o
    let aX ← AlgStr_Tm topnames X
    let dX ← DAlgStr_Tm SF topnames X
    let algS' := if varo.2.2 then sfNopar [algS,sfLit varo.2.1] else algS
    let dY ← DAlgStr_Ty SF (varo.1::topnames) algS' Y
    DAlgArgFmt SF varo.1 aX dX dY


def DAlg_Con_core (SF : StringFormat) : List augTy → StateT Nat Option (List (String × sfExp))
| mkAugTy (Expl s) aT :: augCon => do
    let res ← DAlg_Con_core SF augCon
    let firstname ← DAlgStr_Ty SF (getTopnames augCon) (sfLit s) aT
    return res ++ [(s,firstname)]
| [] => return []
| _ => none


def DAlgStr_Con (SF : StringFormat) (AΓ : List augTy) : List String :=
    match (StateT.run (DAlg_Con_core SF AΓ) 0) with
        | some (ll,_) =>  List.map (λ (s,pe) => SF.collapseFor [SF.dalgFn s, ":", pe.toString]) ll
        | none => []

def DAlgStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (DAlgStr_Con SF)

def DAlgStrElim (SF : StringFormat) := toEliminator (DAlgStrElim_outer SF)

syntax "[DAlgStr|" con_inner "]" : condata_outer
