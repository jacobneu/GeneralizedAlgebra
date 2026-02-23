import GeneralizedAlgebra.typecheck


open Nat
open preTy preTm preArg
open wellCon



def AlgStr_Tm : List String → preTm → String
| As::_, preVAR 0 => As
| _::ss, preVAR (succ n) => AlgStr_Tm ss (preVAR n)
| topnames, preAPP f t =>
    AlgStr_Tm topnames f ++ " " ++ paren (AlgStr_Tm topnames t)
| topnames, preTRANSP _ s => AlgStr_Tm topnames s
| _, _ => ""

def AlgStr_Ty : List String → preTy → List preArg → String
| _, preUU, _ => "Set"
| topnames, preEL t, _ =>
    AlgStr_Tm topnames t
| topnames, preEQ s t, _ =>
    AlgStr_Tm topnames s ++ " = " ++ AlgStr_Tm topnames t
| topnames, prePI _ Y, preAnon TT ::trest =>
    AlgStr_Ty topnames TT [] ++ " → " ++ AlgStr_Ty (""::topnames) Y trest
| topnames, prePI _ Y, preExpl s TT ::trest =>
    "(" ++ s ++ " : " ++ AlgStr_Ty topnames TT [] ++ ") → " ++ AlgStr_Ty (s::topnames) Y trest
| _, _, _ => ""

def AlgStr_Con : GATdata → List String
| ⟨[],_,_⟩ => []
| ⟨[X],[s],[(tt,_)]⟩ =>
    [s ++ " : " ++ AlgStr_Ty [] X tt]
| ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
    AlgStr_Con ⟨XS,ss,tts⟩ ++
    [s ++ " : " ++ AlgStr_Ty ss X tt]
| _ => []
