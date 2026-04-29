import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp sfDecor
open ArgMarker'



def DAlgStr_Tm : List (Option sfExp × Option sfExp) → augTm → StateT Nat Option sfExp
| topnames, augVAR n => Option.join (Prod.snd <$> topnames[n]?)
| topnames, augAPPx f s => do
    let sf ← DAlgStr_Tm topnames f
    let ss ← DAlgStr_Tm topnames s
    return sfL [sf, ss]
| topnames, augAPPi f _ => DAlgStr_Tm topnames f
| topnames, augTRANSP _ s => DAlgStr_Tm topnames s

def DAlgArgFmt : ArgMarker' sfExp → sfExp → sfExp → sfExp → sfExp → Option sfExp
| Expl s, ds, aX, dX, body =>
    sfDep [(Impl s,aX)] $ sfDep [(Expl ds,sfNopar [dX,s])] body
| Impl s, ds, aX, dX, body =>
    sfDep [(Impl s,aX),(Impl ds,sfNopar [dX,s])] body
| _, _, _, _, _ => none

def DAlgStr_Ty : List (Option sfExp × Option sfExp) → sfExp → augTyMarker → StateT Nat Option sfExp
| _, algS, augUU => return sfArr algS sfSet
| topnames, algS, augEL X => (sfL [ · , algS]) <$> DAlgStr_Tm topnames X
| topnames, _, augEQ t1 t2 => do
    let sf1 ← DAlgStr_Tm topnames t1
    let sf2 ← DAlgStr_Tm topnames t2
    return sfEq sf1 sf2
| topnames, algS, augPI o X Y => do
    let varo ← getNameAM o
    let dvar ← sfIdent <$> getName
    let aX ← AlgStr_Tm (topnames.map Prod.fst) X
    let dX ← DAlgStr_Tm topnames X
    let algS' := if varo.2.2 then sfNopar [algS,sfIdent varo.2.1] else algS
    let dY ← DAlgStr_Ty ((sfIdent varo.2.1,dvar)::topnames) algS' Y
    DAlgArgFmt varo.1 dvar aX dX dY


def DAlg_Con_core : List (augTyMarker × Option String × Option String) → StateT Nat Option (List (String × sfExp))
| (aT,os,ods) :: augCon => do
    let s ← os
    let ds ← ods
    let res ← DAlg_Con_core augCon
    let firstname ← DAlgStr_Ty (augCon.map (λ (_,os',ods') => (sfIdent <$> os',sfIdent <$> ods'))) (sfIdent s) aT
    return res ++ [(ds,firstname)]
| [] => return []


def DAlgStr_Con (SF : StringFormat) (AΓ : List augTy) (algNames dalgNames : List String := []): List String :=
    let (origNames,aTs) := (AΓ.map (λ (mkAugTy as aT) => (Option.map SF.identModify $ extractIdent? as,aT))).unzip
    let algNames' := (List.zipWithSnd (Option.elim · · some) (algNames.map SF.identModify) origNames.reverse).reverse
    let dalgNames' := (List.zipWithSnd (Option.elim · · some) (dalgNames.map SF.identModify) (algNames'.map (Option.map SF.dalgFn)).reverse).reverse
    let AΓ' := List.zip aTs (List.zip algNames' dalgNames')
    match (StateT.run (DAlg_Con_core AΓ') 0) with
        | some (ll,_) =>  List.map (OuterToString SF) ll
        | none => []

def DAlgStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (DAlgStr_Con SF)

def DAlgStrElim (SF : StringFormat) := toEliminator (DAlgStrElim_outer SF)

syntax "[DAlgStr|" con_inner "]" : condata_outer
