import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.formats.PseudoAgda

open Nat
open preTy preTm
open elaborator
open basicEliminators
open psExp



-- def AlgStr_Tm : List String → preTm → String
-- | As::_, preVAR 0 => As
-- | _::ss, preVAR (succ n) => AlgStr_Tm ss (preVAR n)
-- | topnames, preAPP f t =>
--     AlgStr_Tm topnames f ++ " " ++ mkParen (AlgStr_Tm topnames t)
-- | topnames, preTRANSP _ s => AlgStr_Tm topnames s
-- | _, _ => ""

-- def AlgStr_Ty : List String → preTy → List (Option (String × Bool) × preTm) → String
-- | _, preUU, _ => "Set"
-- | topnames, preEL t, _ =>
--     AlgStr_Tm topnames t
-- | topnames, preEQ s t, _ =>
--     AlgStr_Tm topnames s ++ " = " ++ AlgStr_Tm topnames t
-- | topnames, prePI _ Y, (none,t) ::trest =>
--     AlgStr_Tm topnames t ++ " → " ++ AlgStr_Ty (""::topnames) Y trest
-- | topnames, prePI _ Y, (some (s,true),t) ::trest =>
--     "(" ++ s ++ " : " ++ AlgStr_Tm topnames t ++ ") → " ++ AlgStr_Ty (s::topnames) Y trest
-- | topnames, prePI _ Y, (some (s,false),_) ::trest =>
--     -- "{" ++ s ++ " : " ++ AlgStr_Tm topnames t ++ "} → " ++
--     AlgStr_Ty (s::topnames) Y trest
-- | _, _, _ => ""


def AlgStr_Tm : List String → preTm → psExp
| As::_, preVAR 0 => psLit As
| _::ss, preVAR (succ n) => AlgStr_Tm ss (preVAR n)
| topnames, preAPP f t =>
    psL [AlgStr_Tm topnames f, AlgStr_Tm topnames t]
| topnames, preTRANSP _ s => AlgStr_Tm topnames s
| _, _ => psLit ""


def AlgStr_Ty : List String → preTy → List (Option (String × Bool)) → psExp
| _, preUU, _ => psLit "Set"
| topnames, preEL t,_ =>
    AlgStr_Tm topnames t
| topnames, preEQ s t,_ =>
    psNopar $ List.map psExp.strictify [AlgStr_Tm topnames s,psLit "=",AlgStr_Tm topnames t]
| topnames, prePI X Y, none ::trest =>
    psNopar [AlgStr_Tm topnames X, psLit "→", AlgStr_Ty (""::topnames) Y trest]
| topnames, prePI X Y, some (s,true) ::trest =>
    match AlgStr_Ty (s::topnames) Y trest with
    | psDep tel body => psDep ((s,AlgStr_Tm topnames X)::tel) body
    | tres => psDep [(s,AlgStr_Tm topnames X)] tres
| topnames, prePI X Y, some (s,false) ::trest =>
    match AlgStr_Ty (s::topnames) Y trest with
    | psDepI tel body => psDepI ((s,AlgStr_Tm topnames X)::tel) body
    | tres => psDepI [(s,AlgStr_Tm topnames X)] tres
| _, _, _ => psLit ""


def AlgStr_Con_core : List String → List (preTy × List (Option (String × Bool))) → List String
| [],_ => []
| [s],[(X,tt)] =>
    [collapseFor $ [s, ":", psExp.toString $ AlgStr_Ty [] X tt]]
| s::ss,(X,tt)::tts =>
    AlgStr_Con_core ss tts ++
    [collapseFor $ [s, ":", psExp.toString $ AlgStr_Ty ss X tt]]
| _,_ => []

def GATdataZip_core : preTy → List (Option (String × Bool)) → preTy × List (Option (String × Bool))
| prePI X Y, o::TT => (prePI X Y,o :: (GATdataZip_core Y TT).2)
| T, _ => (T,[])


def AlgStrElim_outer : eliminator_outer preElim_inner := ⟨
    List String,
    λ Γ topnames telescopes =>
        AlgStr_Con_core (List.reverse topnames) (List.zipWith GATdataZip_core Γ (List.reverse telescopes))
⟩
def AlgStrElim := toEliminator AlgStrElim_outer

syntax "[AlgStr|" "]" : condata_outer
syntax "[AlgStr|" con_inner "]" : condata_outer
