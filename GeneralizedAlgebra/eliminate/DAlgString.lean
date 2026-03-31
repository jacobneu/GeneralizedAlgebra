import GeneralizedAlgebra.eliminate.AlgString


open Nat
open preTy preTm
open wellCon

def dalg s := s ++ "ᴰ"

-- def DAlgStr_Tm : List String → preTm → String
-- | s::ss, preVAR 0

def DAlgStr_Tm : List String → preTm → String
| topnames, preVAR n => dalg (AlgStr_Tm topnames (preVAR n))
| topnames, preAPP f s => DAlgStr_Tm topnames f ++ " " ++ mkParen (AlgStr_Tm topnames s) ++ " " ++ mkParen (DAlgStr_Tm topnames s)
| topnames, preTRANSP _ s => DAlgStr_Tm topnames s

def DAlgStr_Ty : List String → List String → String → preTy → String
| _, _, algS, preUU => algS ++ " → Set"
| topnames, _, algS, preEL tt => DAlgStr_Tm topnames tt ++ " " ++ mkParen algS
| topnames, t::ts, algS, prePI X Y =>
"(" ++ t ++ " : " ++ AlgStr_Tm topnames X ++ ") → (" ++ dalg t ++ " : " ++ DAlgStr_Tm topnames X ++ " " ++ t ++ ") → " ++ DAlgStr_Ty (t::topnames) ts (algS ++ " " ++ t) Y
| topnames, _, _, preEQ s t => DAlgStr_Tm topnames s ++ " = " ++ DAlgStr_Tm topnames t
| _, _, _, _ => ""

def DAlgStr_Con_core : preCon → List (List String) → List String → List String
| [], _, _ => []
| X::XS, tt::tts, s::ss =>
    DAlgStr_Con_core XS tts ss ++ [dalg s ++ " : " ++ DAlgStr_Ty ss tt s X ]
| _,_,_ => []

def genVars_core : Nat → List (List (Option String)) → List (List String) → List (List String)
| _, [],_ => []
| acc, []::AS, given => []::genVars_core acc AS given
-- | acc, []::AS, [] => []::genVars_core acc AS []
| acc, (none::as)::AS, []::givenRest => match genVars_core (succ acc) (as::AS) ([]::givenRest) with
    | headStr::rest => (("X_" ++ toString acc)::headStr)::rest
    | [] => []
| acc, (_::as)::AS, (s1::givenFst)::givenRest => match genVars_core acc (as::AS) (givenFst::givenRest) with
    | headStr::rest => (s1::headStr)::rest
    | [] => []
| acc, (none::as)::AS, [] => match genVars_core (succ acc) (as::AS) [] with
    | headStr::rest => (("X_" ++ toString acc)::headStr)::rest
    | [] => []
-- | acc, (_::as)::AS, (s1::givenFst)::givenRest => match genVars_core acc (as::AS) (givenFst::givenRest) with
--     | headStr::rest => (s1::headStr)::rest
--     | [] => []
| acc, ((some s)::as)::AS, [] => match genVars_core acc (as::AS) [] with
    | headStr::rest => (s::headStr)::rest
    | [] => []
| acc, ((some s)::as)::AS, ([]::givenRest) => match genVars_core acc (as::AS) ([]::givenRest) with
    | headStr::rest => (s::headStr)::rest
    | [] => []

def genVars (input : List (List (Option String))) (given : List (List String) := []) : List (List String) := genVars_core 0 (List.reverse input) given

def DAlgStr_Con (𝔊 : GATdata) (teleNames : List (List String) := []): List String :=
let telescopeNames := List.reverse (genVars 𝔊.telescopes teleNames)
DAlgStr_Con_core 𝔊.con telescopeNames (List.reverse 𝔊.topnames)
