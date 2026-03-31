import GeneralizedAlgebra.nouGAT


open Nat
open preTy preTm
open elaborator
open basicEliminators



def AlgStr_Tm : List String → preTm → String
| As::_, preVAR 0 => As
| _::ss, preVAR (succ n) => AlgStr_Tm ss (preVAR n)
| topnames, preAPP f t =>
    AlgStr_Tm topnames f ++ " " ++ mkParen (AlgStr_Tm topnames t)
| topnames, preTRANSP _ s => AlgStr_Tm topnames s
| _, _ => ""

def AlgStr_Ty : List String → preTy → List (Option String × preTm) → String
| _, preUU, _ => "Set"
| topnames, preEL t, _ =>
    AlgStr_Tm topnames t
| topnames, preEQ s t, _ =>
    AlgStr_Tm topnames s ++ " = " ++ AlgStr_Tm topnames t
| topnames, prePI _ Y, (none,t) ::trest =>
    AlgStr_Tm topnames t ++ " → " ++ AlgStr_Ty (""::topnames) Y trest
| topnames, prePI _ Y, (some s,t) ::trest =>
    "(" ++ s ++ " : " ++ AlgStr_Tm topnames t ++ ") → " ++ AlgStr_Ty (s::topnames) Y trest
| _, _, _ => ""

def AlgStr_Con_core : List String → List (preTy × List (Option String × preTm)) → List String
| [s],[(X,tt)] =>
    [s ++ " : " ++ AlgStr_Ty [] X tt]
| s::ss, (X,tt)::rest => -- ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
    AlgStr_Con_core ss rest ++
    [s ++ " : " ++ AlgStr_Ty ss X tt]
| _,_ => []

def GATdataZip_core : preTy → List (Option String) → preTy × List (Option String × preTm)
| prePI X Y, o::TT => (prePI X Y,(o,X) :: (GATdataZip_core Y TT).2)
| T, _ => (T,[])

def GATdataZip : GATdata → List String × List (preTy × List (Option String × preTm))
| ⟨thePreCon, theTopnames, theTelescopes⟩ =>
    (List.reverse theTopnames, List.zipWith GATdataZip_core thePreCon (List.reverse theTelescopes))

def AlgStr_Con (𝔊 : GATdata) : List String := let z := GATdataZip 𝔊; AlgStr_Con_core z.1 z.2


def AlgStrElim_outer : eliminator_outer preElim_inner := ⟨
    List String,
    λ Γ topnames telescopes =>
        AlgStr_Con_core (List.reverse topnames) (List.zipWith GATdataZip_core Γ (List.reverse telescopes))
⟩
def AlgStrElim := toEliminator AlgStrElim_outer

syntax "[AlgStr|" "]" : condata_outer
syntax "[AlgStr|" con_inner "]" : condata_outer
