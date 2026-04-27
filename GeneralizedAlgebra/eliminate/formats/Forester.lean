import GeneralizedAlgebra.eliminate.formats.StringFormat




def identFormat : String → String
| "Γ" => "#{\\Gamma}"
| "Δ" => "#{\\Delta}"
| "Θ" => "#{\\Theta}"
| "Ξ" => "#{\\Xi}"
| "γ" => "#{\\gamma}"
| "ϑ" => "#{\\vartheta}"
| "σ" => "#{\\sigma}"
| "δ" => "#{\\delta}"
| "ε" => "#{\\epsilon}"
| "η" => "#{\\eta}"
| "π" => "#{\\pi}"
| "π₀" => "#{\\pi_0}"
| "π₁" => "#{\\pi_1}"
| "π₂" => "#{\\pi_2}"
| "ηε" => "#{\\eta\\epsilon}"
| s => "\\mathsf{" ++ s ++ "}"

open sfDecor

def forDecorate (s : String) : sfDecor → String
| sfId => s
| sfAlg => s ++ "\\alg"
| sfOne => s ++ "_1"
| sfDalg => s ++ "\\dalg"
| sfHom => s ++ "\\hom"
| sfSect => s ++ "\\sect"
| sfZero => s ++ "_0"

def liFormat s := "\\li{#{" ++ s ++ "}}"

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
| sfId => (["\\taxon{Definition}","","\\import{index}","\\title{#{\\mathfrak{" ++ G ++ "}}}","\\p{The GAT #{\\GAT{" ++ G ++ "}} is given by the signature","\\<html:ul>[style]{list-style-type:'▷  ';list-style-position: inside;}{","\\<html:li>[style]{list-style-type:'◇';list-style-position: outside;}{}"],["}","}"])
| sfAlg => (["\\taxon{Definition}","","\\import{index}","\\title{#{\\Alg{" ++ G ++ "}}}","\\p{A \\strong{\\GAT{" ++ G ++ "}-algebra} consists of","\\ul{"],["}","}"])
| sfDalg => (["\\taxon{Definition}","","\\import{index}","\\title{#{\\DAlg{" ++ G ++ "}}}","\\p{A \\strong{displayed \\GAT{" ++ G ++ "}-algebra} ", "(over a \\GAT{" ++ G ++ "}-algebra " ++ inlineAlgFmt identFormat topnames ++ ")","consists of","\\ul{"],["}","}"])
| sfSect => (["\\taxon{Definition}","","\\import{index}","\\title{#{\\Sect{" ++ G ++ "}}}","\\p{A \\strong{section} of a displayed \\GAT{" ++ G ++ "}-algebra " ++ inlineAlgFmt (λ s => identFormat s ++ "\\dalg") topnames ++ " (over a \\GAT{" ++ G ++ "}-algebra " ++ inlineAlgFmt identFormat topnames ++ ")","consists of","\\ul{"],["}","}"])
| sfHom => (["\\taxon{Definition}","","\\import{index}","\\title{#{\\Hom{" ++ G ++ "}}}","\\p{A \\strong{homomorphism} of \\GAT{" ++ G ++ "}-algebras (from " ++ inlineAlgFmt (λ s => identFormat s ++ "_0") topnames ++ " to " ++ inlineAlgFmt (λ s => identFormat s ++ "_1") topnames ++ ")","consists of","\\ul{"],["}","}"])
| _ => ([],[])


def forester : StringFormat := ⟨
    λ s => paren' "\\;" [s] ["\\;"],
    String.intercalate "\\;",
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
    (String.intercalate "\\;" ["\\Pi",·,·]),
    "\\Eq",
    "\\El",
    "@",
    "\\transp",
    "[wk]",
    forFormatWrapping,
    forFormatLine
⟩
