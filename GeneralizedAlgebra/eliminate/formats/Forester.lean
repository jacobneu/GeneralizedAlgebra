import GeneralizedAlgebra.eliminate.formats.StringFormat


def charSFIdentFormat : Char → String
| 'Γ' => "\\Gamma"
| 'Δ' => "\\Delta"
| 'Θ' => "\\Theta"
| 'Ξ' => "\\Xi"
| 'γ' => "\\gamma"
| 'ϑ' => "\\vartheta"
| 'σ' => "\\sigma"
| 'δ' => "\\delta"
| 'ε' => "\\epsilon"
| 'η' => "\\eta"
| 'β' => "\\beta"
| 'π' => "\\pi"
| '_' => "\\_"
| '(' => "\\lparen{}"
| ')' => "\\rparen{}"
| '₀' => "_0"
| '₁' => "_1"
| '₂' => "_2"
| c => "\\mathsf{" ++ [c].asString ++ "}"

def charIdentFormat : Char → String
| 'Γ' => "\\Gamma"
| 'Δ' => "\\Delta"
| 'Θ' => "\\Theta"
| 'Ξ' => "\\Xi"
| 'γ' => "\\gamma"
| 'ϑ' => "\\vartheta"
| 'σ' => "\\sigma"
| 'δ' => "\\delta"
| 'ε' => "\\epsilon"
| 'η' => "\\eta"
| 'β' => "\\beta"
| 'π' => "\\pi"
-- | '_' => "\\_"
| '(' => "\\lparen{}"
| ')' => "\\rparen{}"
| '₀' => "_0"
| '₁' => "_1"
| '₂' => "_2"
| c => [c].asString



def strCombine (s1 s2 : String) : String := match (s1.toList,s2.toList) with
| ('\\'::'m'::'a'::'t'::'h'::'s'::'f'::'{'::rest1,'\\'::'m'::'a'::'t'::'h'::'s'::'f'::'{'::rest2) => "\\mathsf{" ++ rest1.dropLast.asString ++ rest2.asString
| _ => s1 ++ s2

def spaceIntercal (s1 s2 : String) : String := match (s1.toList.reverse,s2.toList) with
| (_,'\\'::'t'::'o'::_) => s1 ++ " " ++ s2
| (_,'\\'::'c'::'o'::'l'::'o'::'n'::_) => s1 ++ " " ++ s2
| ('n'::'o'::'l'::'o'::'c'::'\\'::_,_) => s1 ++ " " ++ s2
| ('o'::'t'::'\\'::_,_) => s1 ++ " " ++ s2
| (_,[]) => s1
| ([],_) => s2
| _ => s1 ++ "\\;" ++ s2

def identFormat (s : String) : String := List.foldr strCombine "" (s.toList.map charSFIdentFormat)

open sfDecor

def forDecorate (s : String) : sfDecor → String
| sfId => s
| sfAlg => s ++ "\\alg"
| sfOne => s ++ "_1"
| sfDalg => s ++ "\\dalg"
| sfHom => s ++ "\\hom"
| sfSect => s ++ "\\sect"
| sfZero => s ++ "_0"

def liFormat (s : String) := "\\li{#{" ++ List.foldr strCombine "" (s.toList.map charIdentFormat) ++ "}}"

def forFormatLine (s : String) : sfDecor → String
| sfId => liFormat s
| _ => liFormat s
-- | _ => "   " ++ s

def inlineAlgFmt : (String → String) → List String → String
| _,[] => ""
| f,[x] => "#{" ++ f x ++ "}"
| f,[x,y] => "#{(" ++ f x ++ ", " ++ f y ++ ")}"
| f,[x,y,z] => "#{(" ++ f x ++ ", " ++ f y ++ ", " ++ f z ++ ")}"
| f,l => "#{(" ++ String.intercalate ", " (List.map f (l.take 3)) ++ ", \\ldots)}"

def forFormatWrapping (G _ : String) (topnames : List String) : sfDecor → List String × List String
| sfId => (["\\p{The GAT #{\\GAT{" ++ G ++ "}} is given by the signature","\\<html:ul>[style]{list-style-type:'▷  ';list-style-position: inside;}{","\\<html:li>[style]{list-style-type:'◇';list-style-position: outside;}{}"],["}","}"])
| sfAlg => (["\\p{A \\strong{\\GAT{" ++ G ++ "}-algebra} consists of","\\ul{"],["}","}"])
| sfDalg => (["\\p{A \\strong{displayed \\GAT{" ++ G ++ "}-algebra} ", "(over a \\GAT{" ++ G ++ "}-algebra " ++ inlineAlgFmt identFormat topnames ++ ")","consists of","\\ul{"],["}","}"])
| sfSect => (["\\p{A \\strong{section} of a displayed \\GAT{" ++ G ++ "}-algebra " ++ inlineAlgFmt (λ s => identFormat s ++ "\\dalg") topnames ++ " (over a \\GAT{" ++ G ++ "}-algebra " ++ inlineAlgFmt identFormat topnames ++ ")","consists of","\\ul{"],["}","}"])
| sfHom => (["\\p{A \\strong{homomorphism} of \\GAT{" ++ G ++ "}-algebras (from " ++ inlineAlgFmt (λ s => identFormat s ++ "_0") topnames ++ " to " ++ inlineAlgFmt (λ s => identFormat s ++ "_1") topnames ++ ")","consists of","\\ul{"],["}","}"])
| _ => ([],[])


def insertBreak (s : String) : String := match s.toList with
| '('::rest => "\\lparen{}}#{" ++ rest.asString
| _ => s

def forester : StringFormat := ⟨
    λ s => paren' "\\;" [s] ["\\;"],
    List.foldl spaceIntercal "",
    forDecorate,
    identFormat,
    "\\Set",
    "=",
    "\\to",
    "⊤",
    "\\colon",
    "\\{",
    "\\}",
    "\\UU",
    (List.foldl spaceIntercal "" ["\\Pi",·,insertBreak ·]),
    "\\Eq",
    "\\El",
    "@",
    "\\transp",
    "[wk]",
    forFormatWrapping,
    forFormatLine,
    "} #{"
⟩
