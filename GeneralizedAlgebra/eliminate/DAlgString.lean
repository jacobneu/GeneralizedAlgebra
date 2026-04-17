import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp sfDecor
open ArgMarker'



def DAlgStr_Tm : List (Option sfExp) → augTm → StateT Nat Option sfExp
| topnames, augVAR n => (sfDec · sfDalg) <$> Option.join topnames[n]?
| topnames, augAPPx f s => do
    let sf ← DAlgStr_Tm topnames f
    let ss ← DAlgStr_Tm topnames s
    return sfL [sf, ss]
| topnames, augAPPi f _ => DAlgStr_Tm topnames f
| topnames, augTRANSP _ s => DAlgStr_Tm topnames s

def DAlgArgFmt : ArgMarker' sfExp → sfExp → sfExp → sfExp → Option sfExp
| Expl s, aX, dX, body =>
    sfDep [(Impl s,aX)] $ sfDep [(Expl (sfDec s sfDalg),sfNopar [dX,s])] body
| Impl s, aX, dX, body =>
    sfDep [(Impl s,aX),(Impl (sfDec s sfDalg),sfNopar [dX,s])] body
| _, _, _, _ => none

def DAlgStr_Ty : List (Option sfExp) → sfExp → augTyMarker → StateT Nat Option sfExp
| _, algS, augUU => return sfArr algS sfSet
| topnames, algS, augEL X => (sfL [ · , algS]) <$> DAlgStr_Tm topnames X
| topnames, _, augEQ t1 t2 => do
    let sf1 ← DAlgStr_Tm topnames t1
    let sf2 ← DAlgStr_Tm topnames t2
    return sfEq sf1 sf2
| topnames, algS, augPI o X Y => do
    let varo ← getNameAM o
    let aX ← AlgStr_Tm topnames X
    let dX ← DAlgStr_Tm topnames X
    let algS' := if varo.2.2 then sfNopar [algS,sfIdent varo.2.1] else algS
    let dY ← DAlgStr_Ty (sfIdent varo.2.1::topnames) algS' Y
    DAlgArgFmt varo.1 aX dX dY


def DAlg_Con_core : List (Option String × augTyMarker) → StateT Nat Option (List (String × sfExp))
| (os,aT) :: augCon => do
    let s ← os
    let res ← DAlg_Con_core augCon
    let firstname ← DAlgStr_Ty (augCon.map (λ (os',_) => sfIdent <$> os')) (sfIdent s) aT
    return res ++ [(s,firstname)]
| [] => return []


def DAlgStr_Con (SF : StringFormat) (AΓ : List augTy) (algNames : List String := []): List String :=
    let AΓ' := (List.zipWithSnd (λ os (mkAugTy as aT) => Option.elim os (extractIdent? as,aT) (some ·,aT)) algNames AΓ.reverse).reverse
    match (StateT.run (DAlg_Con_core AΓ') 0) with
        | some (ll,_) =>  List.map (OuterToString SF sfDalg) ll
        | none => []

def DAlgStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (DAlgStr_Con SF)

def DAlgStrElim (SF : StringFormat) := toEliminator (DAlgStrElim_outer SF)

syntax "[DAlgStr|" con_inner "]" : condata_outer
