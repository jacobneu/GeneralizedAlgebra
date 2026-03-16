import GeneralizedAlgebra.eliminate.ConForester


open Nat
open preTy preTm preArg
open wellCon



def AlgForester_Tm : List String → preTm → String
| As::_, preVAR 0 => identFormat As
| _::ss, preVAR (succ n) => AlgForester_Tm ss (preVAR n)
| topnames, preAPP f t =>
    AlgForester_Tm topnames f ++ " " ++ paren (AlgForester_Tm topnames t)
| topnames, preTRANSP _ s => AlgForester_Tm topnames s
| _, _ => ""

def AlgForester_Ty : List String → preTy → List preArg → String
| _, preUU, _ => "\\Set"
| topnames, preEL t, _ =>
    AlgForester_Tm topnames t
| topnames, preEQ s t, _ =>
    AlgForester_Tm topnames s ++ " = " ++ AlgForester_Tm topnames t
| topnames, prePI _ Y, preAnon TT ::trest =>
    AlgForester_Ty topnames TT [] ++ " \\to " ++ AlgForester_Ty (""::topnames) Y trest
| topnames, prePI _ Y, preExpl s TT ::trest =>
    "(" ++ identFormat s ++ " : " ++ AlgForester_Ty topnames TT [] ++ ") \\to " ++ AlgForester_Ty (s::topnames) Y trest
| _, _, _ => ""

def AlgForester_Con : GATdata → List String
| ⟨[],_,_⟩ => []
| ⟨[X],[s],[(tt,_)]⟩ =>
    [identFormat s ++ " \\colon " ++ AlgForester_Ty [] X tt]
| ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
    AlgForester_Con ⟨XS,ss,tts⟩ ++
    [identFormat s ++ " \\colon " ++ AlgForester_Ty ss X tt]
| _ => []


def AlgForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\Alg{" ++ G ++ "}}}"]
++ ["\\p{A \\strong{#{" ++ G ++ "}-algebra} consists of","\\ul{"]
++ List.map liFormat (AlgForester_Con 𝔊)
++ ["}","}"]
-- | ⟨[],_,_⟩ => []
-- | ⟨[X],[s],[(tt,_)]⟩ =>
--     [s ++ " : " ++ AlgForester_Ty [] X tt]
-- | ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
--     AlgForester_Con ⟨XS,ss,tts⟩ ++
--     [s ++ " : " ++ AlgForester_Ty ss X tt]
-- | _ => []
