import GeneralizedAlgebra.eliminate.ConForester


open Nat
open preTy preTm preArg
open wellCon



def AlgForester_Tm : List String → preTm → List String
| As::_, preVAR 0 => [As]
| _::ss, preVAR (succ n) => AlgForester_Tm ss (preVAR n)
| topnames, preAPP f t =>
    [collapseFor (AlgForester_Tm topnames f), parenFor (AlgForester_Tm topnames t)]
| topnames, preTRANSP _ s => AlgForester_Tm topnames s
| _, _ => []

def AlgForester_Ty : Nat → List String → preTy → List preArg → List String
| _,_, preUU, _ => ["\\Set"]
| _,topnames, preEL t, _ =>
    AlgForester_Tm topnames t
| _,topnames, preEQ s t, _ =>
    [collapseFor (AlgForester_Tm topnames s),"=",collapseFor (AlgForester_Tm topnames t)]
| succ n,topnames, prePI _ Y, preAnon TT ::trest =>
    AlgForester_Ty n topnames TT [] ++ ["\\to"] ++ AlgForester_Ty n (""::topnames) Y trest
| succ n,topnames, prePI X (prePI X' (prePI X'' Y)), preExpl s TT :: preExpl s' TT' :: preExpl s'' TT'' :: trest =>
    if X' = preWkTm X then
        if X'' = preWkTm X' then
            ["(" ++ s ++ "\\;" ++ s' ++ "\\;" ++ s'' ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Ty n topnames TT []) ++ ")","\\to"] ++ AlgForester_Ty n (s''::s'::s::topnames) Y trest
        else
            ["(" ++ s ++ "\\;" ++ s' ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Ty n topnames TT []) ++ ")"] ++ AlgForester_Ty n (s'::s::topnames) (prePI X'' Y) (preExpl s'' TT'' :: trest)
    else
        ["(" ++ s ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Ty n topnames TT []) ++ ")"] ++ AlgForester_Ty n (s::topnames) (prePI X' (prePI X'' Y)) (preExpl s' TT' :: preExpl s'' TT'' :: trest)
| succ n, topnames, prePI X (prePI X' Y), preExpl s TT :: preExpl s' TT' :: trest =>
    if X' = preWkTm X
    then ["(" ++ s ++ "\\;" ++ s' ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Ty n topnames TT []) ++ ")","\\to"] ++ AlgForester_Ty n (s'::s::topnames) Y trest
    else ["(" ++ s ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Ty n topnames TT []) ++ ")"] ++ AlgForester_Ty n (s::topnames) (prePI X' Y) (preExpl s' TT' :: trest)
| succ n, topnames, prePI _ Y, preExpl s TT ::trest =>
    ["(" ++ s ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Ty n topnames TT []) ++ ")","\\to"] ++ AlgForester_Ty n (s::topnames) Y trest
| _, _, _, _ => []

def AlgForester_Con_core : preCon → List String → List (List preArg × preTy) → List String
| [],_,_ => []
| [X],[s],[(tt,_)] =>
    [collapseFor $ s :: "\\colon" :: AlgForester_Ty 10000 [] X tt]
| X::XS,s::ss,(tt,_)::tts =>
    AlgForester_Con_core XS ss tts ++
    [collapseFor $ s :: "\\colon" :: AlgForester_Ty 10000 ss X tt]
| _,_,_ => []

def AlgForester_Con (𝔊 : GATdata) : List String :=
    AlgForester_Con_core 𝔊.con (List.map identFormat 𝔊.topnames) 𝔊.telescopes

def AlgForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\Alg{" ++ G ++ "}}}"]
++ ["\\p{A \\strong{\\GAT{" ++ G ++ "}-algebra} consists of","\\ul{"]
++ List.map liFormat (AlgForester_Con 𝔊)
++ ["}","}"]
-- | ⟨[],_,_⟩ => []
-- | ⟨[X],[s],[(tt,_)]⟩ =>
--     [s ++ " : " ++ AlgForester_Ty [] X tt]
-- | ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
--     AlgForester_Con ⟨XS,ss,tts⟩ ++
--     [s ++ " : " ++ AlgForester_Ty ss X tt]
-- | _ => []
