import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.AlgForester
import GeneralizedAlgebra.signatures.category


open Nat
open preTy preTm preArg
open wellCon
open texExp

def dalgFor sl := (parenFor sl) ++ "\\dalg"
def dalgFn s := s ++ "\\dalg"


def DAlgForester_Tm : List String → preTm → texExp
| topnames, preVAR n => texDecorate (AlgForester_Tm topnames (preVAR n)) dalgFn
| topnames, preAPP f s => texL [DAlgForester_Tm topnames f, AlgForester_Tm topnames s, DAlgForester_Tm topnames s]
| topnames, preTRANSP _ s => DAlgForester_Tm topnames s


def DAlgForester_Ty : List String → List String → texExp → preTy → texExp
| _, _, algS, preUU => texNopar [algS,texLit " \\to ",texLit "\\Set"]
| topnames, _, algS, preEL tt => texL [DAlgForester_Tm topnames tt, algS]
| topnames, t::ts, algS, prePI X Y => match (DAlgForester_Ty (t::topnames) ts (texNopar [algS,texLit t]) Y) with
    | texDep tel body => texDep ((t,AlgForester_Tm topnames X)::(dalgFn t, texNopar [DAlgForester_Tm topnames X,texLit t])::tel) body
    | body => texDep [(t,AlgForester_Tm topnames X),(dalgFn t, texNopar [DAlgForester_Tm topnames X,texLit t])] body
| topnames, _, _, preEQ s t => texNopar $ List.map texExp.strictify [DAlgForester_Tm topnames s,texLit "=",DAlgForester_Tm topnames t]
| _, _, _, _ => texLit ""


def DAlgForester_Con_core : preCon → List (List String) → List String → List String
| [], _, _ => []
| X::XS, tt::tts, s::ss =>
    DAlgForester_Con_core XS tts ss ++ [dalgFor [s] ++ " \\colon " ++ (texExp.toString $ DAlgForester_Ty ss tt (texLit s) X) ]
| _,_,_ => []

def DAlgForester_Con_test : preCon → List (List String) → List String → List texExp
| [], _, _ => []
| X::XS, tt::tts, s::ss =>
    DAlgForester_Con_test XS tts ss ++ [DAlgForester_Ty ss tt (texLit s) X ]
| _,_,_ => []

def DAlgForester_Con (𝔊 : GATdata) (teleNames : List (List String) := []): List String :=
let telescopeNames := List.reverse (genVars 𝔊.telescopes teleNames)
DAlgForester_Con_core 𝔊.con telescopeNames (List.map identFormat 𝔊.topnames)


def DAlgForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\DAlg{" ++ G ++ "}}}"]
++ ["\\p{A \\strong{displayed \\GAT{" ++ G ++ "}-algebra} consists of","\\ul{"]
++ List.map liFormat (DAlgForester_Con 𝔊)
++ ["}","}"]
