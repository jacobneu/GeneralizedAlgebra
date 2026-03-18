import GeneralizedAlgebra.eliminate.ConForester

open Nat
open preTy preTm preArg
open wellCon
open texExp


def AlgForester_Tm : List String → preTm → texExp
| As::_, preVAR 0 => texLit As
| _::ss, preVAR (succ n) => AlgForester_Tm ss (preVAR n)
| topnames, preAPP f t =>
    texL [AlgForester_Tm topnames f, AlgForester_Tm topnames t]
| topnames, preTRANSP _ s => AlgForester_Tm topnames s
| _, _ => texLit ""


def AlgForester_Ty : Nat → List String → preTy → List preArg → texExp
| _,_, preUU, _ => texLit "\\Set"
| _,topnames, preEL t, _ =>
    AlgForester_Tm topnames t
| _,topnames, preEQ s t, _ =>
    texNopar $ List.map texExp.strictify [AlgForester_Tm topnames s,texLit "=",AlgForester_Tm topnames t]
| succ n,topnames, prePI _ Y, preAnon TT ::trest =>
    texNopar [AlgForester_Ty n topnames TT [], texLit "\\to", AlgForester_Ty n (""::topnames) Y trest]
| succ n, topnames, prePI _ Y, preExpl s TT ::trest =>
    match AlgForester_Ty n (s::topnames) Y trest with
    | texDep tel body => texDep ((s,AlgForester_Ty n topnames TT [])::tel) body
    | tres => texDep [(s,AlgForester_Ty n topnames TT [])] tres
| _, _, _, _ => texLit ""

def AlgForester_Con_core : preCon → List String → List (List preArg × preTy) → List String
| [],_,_ => []
| [X],[s],[(tt,_)] =>
    [collapseFor $ [s, "\\colon", texExp.toString $ AlgForester_Ty 10000 [] X tt]]
| X::XS,s::ss,(tt,_)::tts =>
    AlgForester_Con_core XS ss tts ++
    [collapseFor $ [s, "\\colon", texExp.toString $ AlgForester_Ty 10000 ss X tt]]
| _,_,_ => []

-- def AlgForester_Con_test : preCon → List String → List (List preArg × preTy) → List texExp
-- | [],_,_ => []
-- | [X],_,[(tt,_)] =>
--     [AlgForester_Ty 10000 [] X tt]
-- | X::XS,_::ss,(tt,_)::tts =>
--     AlgForester_Con_test XS ss tts ++
--     [AlgForester_Ty 10000 ss X tt]
-- | _,_,_ => []

def AlgForester_Con (𝔊 : GATdata) : List String :=
    AlgForester_Con_core 𝔊.con (List.map identFormat 𝔊.topnames) 𝔊.telescopes

def AlgForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\Alg{" ++ G ++ "}}}"]
++ ["\\p{A \\strong{\\GAT{" ++ G ++ "}-algebra} consists of","\\ul{"]
++ List.map liFormat (AlgForester_Con 𝔊)
++ ["}","}"]
