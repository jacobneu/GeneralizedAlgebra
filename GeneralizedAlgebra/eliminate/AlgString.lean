import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.formats.PseudoAgda

open Nat
open elaborator
open basicEliminators
open augTy augTm
open psExp


def AlgStr_Tm : List String → augTm → psExp
| As::_, augVAR 0 => psLit As
| _::ss, augVAR (succ n) => AlgStr_Tm ss (augVAR n)
| topnames, augAPPx f t =>
    psL [AlgStr_Tm topnames f, AlgStr_Tm topnames t]
| topnames, augAPPi f _ => AlgStr_Tm topnames f
| topnames, augTRANSP _ s => AlgStr_Tm topnames s
| _, _ => psLit ""


def AlgStr_Ty : List String → augTy → List (Option (String × Bool)) → psExp
| _, augUU, _ => psLit "Set"
| topnames, augEL t,_ =>
    AlgStr_Tm topnames t
| topnames, augEQ s t,_ =>
    psNopar $ List.map psExp.strictify [AlgStr_Tm topnames s,psLit "=",AlgStr_Tm topnames t]
| topnames, augPIx X Y, none ::trest =>
    psNopar [AlgStr_Tm topnames X, psLit "→", AlgStr_Ty (""::topnames) Y trest]
| topnames, augPIx X Y, some (s,true) ::trest =>
    match AlgStr_Ty (s::topnames) Y trest with
    | psDep tel body => psDep ((s,AlgStr_Tm topnames X)::tel) body
    | tres => psDep [(s,AlgStr_Tm topnames X)] tres
| topnames, augPIi X Y, some (s,false) ::trest =>
    match AlgStr_Ty (s::topnames) Y trest with
    | psDepI tel body => psDepI ((s,AlgStr_Tm topnames X)::tel) body
    | tres => psDepI [(s,AlgStr_Tm topnames X)] tres
| _, _, _ => psLit ""


def AlgStr_Con_core : List String → List (augTy × List (Option (String × Bool))) → List String
| [],_ => []
| [s],[(X,tt)] =>
    [collapseFor $ [s, ":", psExp.toString $ AlgStr_Ty [] X tt]]
| s::ss,(X,tt)::tts =>
    AlgStr_Con_core ss tts ++
    [collapseFor $ [s, ":", psExp.toString $ AlgStr_Ty ss X tt]]
| _,_ => []

def GATdataZip_core : augTy → List (Option (String × Bool)) → augTy × List (Option (String × Bool))
| augPIx X Y, o::TT => (augPIx X Y,o :: (GATdataZip_core Y TT).2)
| augPIi X Y, o::TT => (augPIi X Y,o :: (GATdataZip_core Y TT).2)
| T, _ => (T,[])


def AlgStrElim_outer : eliminator_outer augElim_inner := ⟨
    List String,
    λ Γ topnames telescopes =>
        AlgStr_Con_core (List.reverse topnames) (List.zipWith GATdataZip_core Γ (List.reverse telescopes))
⟩
def AlgStrElim := toEliminator AlgStrElim_outer

syntax "[AlgStr|" con_inner "]" : condata_outer
