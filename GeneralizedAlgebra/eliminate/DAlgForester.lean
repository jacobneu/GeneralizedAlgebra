import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.AlgForester


open Nat
open preTy preTm preArg
open wellCon

def dalgFor sl := (parenFor sl) ++ "\\dalg"

-- def DAlgForester_Tm : List String → preTm → String
-- | s::ss, preVAR 0

def DAlgForester_Tm : List String → preTm → List String
| topnames, preVAR n => [dalgFor (AlgForester_Tm topnames (preVAR n))]
| topnames, preAPP f s => [collapseFor (DAlgForester_Tm topnames f), parenFor (AlgForester_Tm topnames s), parenFor (DAlgForester_Tm topnames s)]
| topnames, preTRANSP _ s => DAlgForester_Tm topnames s

def DAlgForester_Ty : List String → List String → String → preTy → List String
| _, _, algS, preUU => algS :: ["\\to","\\Set"]
| topnames, _, algS, preEL tt => DAlgForester_Tm topnames tt ++ [algS]
| topnames, t::ts, algS, prePI X₀ (prePI X₁ Y) =>
("(" ++ t ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Tm topnames X₀) ++ ")" )
:: ("(" ++ dalgFor [t] ++ "\\;\\colon\\;" ++ collapseFor (DAlgForester_Tm topnames X₀) ++ "\\;" ++ t ++ ") ")
:: DAlgForester_Ty (t::topnames) ts (algS ++ "\\;" ++ t) (prePI X₁ Y)
| topnames, t::ts, algS, prePI X Y =>
("(" ++ t ++ "\\;\\colon\\;" ++ collapseFor (AlgForester_Tm topnames X) ++ ")" )
:: ("(" ++ dalgFor [t] ++ "\\;\\colon\\;" ++ collapseFor (DAlgForester_Tm topnames X) ++ "\\;" ++ t ++ ") ")
:: " \\to "
:: DAlgForester_Ty (t::topnames) ts (parenFor [algS,t]) Y
| topnames, _, _, preEQ s t => [collapseFor (DAlgForester_Tm topnames s),"=",collapseFor (DAlgForester_Tm topnames t)]
| _, _, _, _ => []

def DAlgForester_Con_core : preCon → List (List String) → List String → List String
| [], _, _ => []
| X::XS, tt::tts, s::ss =>
    DAlgForester_Con_core XS tts ss ++ [collapseFor $ dalgFor [s] :: "\\colon" :: DAlgForester_Ty ss tt s X ]
| _,_,_ => []


def DAlgForester_Con (𝔊 : GATdata) (teleNames : List (List String) := []): List String :=
let telescopeNames := List.reverse (genVars 𝔊.telescopes teleNames)
DAlgForester_Con_core 𝔊.con telescopeNames (List.map identFormat 𝔊.topnames)


def DAlgForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\DAlg{" ++ G ++ "}}}"]
++ ["\\p{A \\strong{displayed \\GAT{" ++ G ++ "}-algebra} consists of","\\ul{"]
++ List.map liFormat (DAlgForester_Con 𝔊)
++ ["}","}"]
