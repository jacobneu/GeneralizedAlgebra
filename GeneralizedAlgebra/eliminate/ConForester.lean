import GeneralizedAlgebra.typecheck


open Nat
open preTy preTm preArg


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

def liFormat s := "\\li{#{" ++ s ++ "}}"

-- def wkStr (s : String) : String :=
-- match s.toNat? with
-- | (some n) => Nat.repr (succ n)
-- | _ => s ++ "[wk]"

def parenFor sl := paren' "\\;" sl ["\\;"]
def collapseFor := String.intercalate "\\;"

inductive texExp : Type where
| texLit : String → texExp
| texL : List texExp → texExp -- be lazy about parens on the first
| texR :  List texExp → texExp -- be lazy about parens on the last
| texPar : List texExp → texExp -- be strict about parens
| texNopar : List texExp → texExp -- don't require parens
| texDep : List (String × texExp) → texExp → texExp
| texDecorate : texExp → (String → String) → texExp
open texExp

def texExp.reprPrec : texExp → Nat → String
| texLit s, _ => "texLit(" ++ s ++ ")"
| texL xs, succ i => "texL [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| texR xs, succ i => "texR [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| texPar xs, succ i => "texPar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| texDep tel body, succ i => "texDep [" ++ String.intercalate "," (List.map (λ (s,t) => "(" ++ s ++ "," ++ reprPrec t i ++ ")") tel) ++ "] (" ++ reprPrec body i ++ ")"
| texDecorate t _, succ i => "texDecorate (" ++ reprPrec t i ++ ") _"
| texNopar xs, succ i => "texNopar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| _ , 0 => "ZERO"

instance : Repr texExp where
  reprPrec := λ t _ => texExp.reprPrec t 100000



def ConForester_Tm : preTm → texExp
| preAPP f t => texL [ConForester_Tm f,texLit "@", ConForester_Tm t]
| preVAR n => texLit $ Nat.repr n
| preTRANSP eq y => texPar [texLit "\\transp", ConForester_Tm eq,ConForester_Tm y]



def ConForester_Ty : preTy → texExp
| preUU => texLit "\\UU"
| preEQ s t => texPar [texLit "\\Eq", ConForester_Tm s, ConForester_Tm t]
| preEL X => texL [texLit "\\El", ConForester_Tm X]
| prePI X Y => texL [texLit "\\Pi", ConForester_Tm X, ConForester_Ty Y]


mutual
def texExp.toStringParen : Nat → texExp → String
| _, texLit s => s
| succ n, texR [x] => texExp.toString_core n x
| succ n, texPar [x] => texExp.toString_core n x
| succ n, texNopar [x] => texExp.toString_core n x
| succ n, texL [x] => texExp.toString_core n x
| succ n, texDecorate x f => f (texExp.toStringParen n x)
| _, texR [] => ""
| _, texPar [] => ""
| _, texNopar [] => ""
| _, texL [] => ""
| succ n, z => "(" ++ texExp.toString_core n z ++ ")"
| 0,_ => ""


def groupTel : Nat → List (String × texExp) → List String × String × List (String × texExp)
| _, [] => ([],"",[])
| n, [(i,tt)] => ([i],texExp.toString_core n tt,[])
| n, (i,tt)::(i',tt')::res =>
    let tts := texExp.toString_core n tt
    let tts' := texExp.toString_core n tt'
    if tts = tts'
    then
      let (others,_,remainder) := groupTel n ((i',tt')::res)
      (i::others,tts,remainder)
    else ([i],tts,(i',tt')::res)

def texExp.toString_core : Nat → texExp → String
| _, texLit s => s
| succ n, texL (texL fst :: rest) =>
    texExp.toString_core n (texL fst) ++ "\\;" ++ String.intercalate "\\;" (List.map (texExp.toStringParen n) rest)
| succ n, texL xs => String.intercalate "\\;" (List.map (texExp.toStringParen n) xs)
| succ n, texR [texR xs] => texExp.toString_core n (texR xs)
| succ n, texR [x] => texExp.toStringParen n x
| succ n, texR (x :: xs) => texExp.toStringParen n x ++ "\\;" ++ texExp.toString_core n (texR xs)
| _, texR [] => ""
| succ n, texPar xs => String.intercalate "\\;" (List.map (texExp.toStringParen n) xs)
| succ n, texNopar xs => String.intercalate "\\;" (List.map (texExp.toString_core n) xs)
| succ n, texDep [] body =>  " \\to " ++ texExp.toString_core n body
| succ n, texDep tel body =>
    let (is,tts,remainder) := groupTel (succ n) tel
    "(" ++ String.intercalate "\\;" is ++ " \\colon " ++ tts ++ ")" ++ texExp.toString_core n (texDep remainder body)
| succ n, texDecorate tt f => f (texExp.toString_core n tt)
| 0, _ => ""
end

def texExp.strictify : texExp → texExp
| texNopar xs => texPar xs
| z => z

def texExp.toString : texExp → String := texExp.toString_core 1000000


def ConForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\mathfrak{" ++ G ++ "}}}"]
++ ["\\p{The GAT #{\\GAT{" ++ G ++ "}} is given by the signature"]
++ ["\\<html:ul>[style]{list-style-type:'▷  ';list-style-position: inside;}{","\\<html:li>[style]{list-style-type:'◇';list-style-position: outside;}{}"]
++ List.map liFormat (List.map (λ A => texExp.toString (ConForester_Ty A)) (List.reverse 𝔊.con))
++ ["}","}"]
