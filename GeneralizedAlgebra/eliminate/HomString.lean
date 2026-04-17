import GeneralizedAlgebra.eliminate.AlgString

open Nat
open elaborator
open basicEliminators
open augTy augTm augTyMarker
open sfExp sfDecor
open ArgMarker'



def HomStr_Tm : List (Option sfExp × Option sfExp × Option sfExp) → augTm → Option sfExp
| topnames, augVAR n => Option.join (Prod.snd <$> Prod.snd <$> topnames[n]?)
| topnames, augAPPx f _ => HomStr_Tm topnames f
| topnames, augAPPi f _ => HomStr_Tm topnames f
| topnames, augTRANSP _ s => HomStr_Tm topnames s


def HomStr_Ty : List (Option sfExp × Option sfExp × Option sfExp) → sfExp → sfExp → augTyMarker → StateT Nat Option sfExp
| _, alg0, alg1, augUU => return sfArr alg0 alg1
| topnames, alg0, alg1, augEL X => do
    let sX ← HomStr_Tm topnames X
    return sfEq (sfL [sX, alg0]) alg1
| topnames, alg0, alg1, augPI o X Y => do
    let varo ← getNameAM o
    let hvar ← sfIdent <$> getName
    let aX0 ← AlgStr_Tm (List.map Prod.fst topnames) X
    let hX ← HomStr_Tm topnames X
    let v0 := sfIdent varo.2.1
    let v1 := sfR [hX,v0]
    let alg0' := if varo.2.2 then sfL [alg0,v0] else alg0
    let alg1' := if varo.2.2 then sfL [alg1,v1] else alg1
    let hY ← HomStr_Ty ((v0,v1,hvar)::topnames) alg0' alg1' Y
    return sfDep [(Impl v0,aX0)] hY
| _, _, _, augEQ _ _ => return sfTop


def Hom_Con_core : List (augTyMarker × Option String × Option String × Option String) → StateT Nat Option (List (String × sfExp))
| (aT,o0s,o1s,ohs) :: augCon => do
    let s0 ← o0s
    let s1 ← o1s
    let sh ← ohs
    let res ← Hom_Con_core augCon
    let firstname ← HomStr_Ty (augCon.map (λ (_,o0s',o1s',ohs') => (sfIdent <$> o0s',sfIdent <$> o1s',sfIdent <$> ohs'))) (sfIdent s0) (sfIdent s1) aT
    return res ++ [(sh,firstname)]
| [] => return []


def isntTrivial s := match List.reverse (String.toList s) with
| '⊤'::_ => false
| _ => true

def HomStr_Con (SF : StringFormat) (AΓ : List augTy) (zeroNames oneNames homNames : List String := []): List String :=
    let (origNames,aTs) := (AΓ.map (λ (mkAugTy as aT) => (extractIdent? as,aT))).unzip
    let zeroNames' := (List.zipWithSnd (Option.elim · · some) zeroNames (origNames.map (Option.map SF.zeroFn)).reverse).reverse
    let oneNames' := (List.zipWithSnd (Option.elim · · some) oneNames (origNames.map (Option.map SF.oneFn)).reverse).reverse
    let homNames' := (List.zipWithSnd (Option.elim · · some) homNames (origNames.map (Option.map SF.homFn)).reverse).reverse
    let AΓ' := List.zip aTs (List.zip zeroNames' (List.zip oneNames' homNames'))
    match (StateT.run (Hom_Con_core AΓ') 0) with
        | some (ll,_) =>  List.filter isntTrivial $ List.map (OuterToString SF) ll
        | none => []

def HomStrElim_outer (SF : StringFormat) : eliminator_outer augElim_inner :=
    elimProduct_outer_post augElim_outer (HomStr_Con SF)

def HomStrElim (SF : StringFormat) := toEliminator (HomStrElim_outer SF)

syntax "[HomStr|" con_inner "]" : condata_outer
