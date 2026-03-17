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

def ConForester_Tm : preTm → List String
| preAPP (preAPP (preAPP (preAPP (preAPP f t1) t2) t3) t4) t5 => [parenFor (ConForester_Tm f),"@",parenFor (ConForester_Tm t1),"@",parenFor (ConForester_Tm t2),"@",parenFor (ConForester_Tm t3)," @ ",parenFor (ConForester_Tm t4),"@",parenFor (ConForester_Tm t5)]
| preAPP (preAPP (preAPP (preAPP f t1) t2) t3) t4 => [parenFor (ConForester_Tm f),"@",parenFor (ConForester_Tm t1),"@",parenFor (ConForester_Tm t2),"@",parenFor (ConForester_Tm t3),"@",parenFor (ConForester_Tm t4)]
| preAPP (preAPP (preAPP f t1) t2) t3 => [parenFor (ConForester_Tm f),"@",parenFor (ConForester_Tm t1),"@",parenFor (ConForester_Tm t2),"@",parenFor (ConForester_Tm t3)]
| preAPP (preAPP f t1) t2 => [parenFor (ConForester_Tm f),"@",parenFor (ConForester_Tm t1),"@",parenFor (ConForester_Tm t2)]
| preAPP f t => [parenFor (ConForester_Tm f),"@",parenFor (ConForester_Tm t)]
| preVAR n => [Nat.repr n]
| preTRANSP eq y => ["\\transp",parenFor (ConForester_Tm eq),parenFor (ConForester_Tm y)]

def ConForester_Ty : preTy → List String
| preUU => ["\\UU"]
| preEQ s t => ["\\Eq",parenFor (ConForester_Tm s), parenFor (ConForester_Tm t)]
| preEL X => ["\\El",parenFor (ConForester_Tm X)]
| prePI X Y => ["\\Pi",parenFor (ConForester_Tm X), parenFor (ConForester_Ty Y)]

-- def ConForester_Tm : List String → preTm → String
-- | As::_, preVAR 0 => identFormat As
-- | _::ss, preVAR (succ n) => ConForester_Tm ss (preVAR n)
-- | topnames, preAPP f t =>
--     ConForester_Tm topnames f ++ " " ++ parenFor (ConForester_Tm topnames t)
-- | topnames, preTRANSP _ s => ConForester_Tm topnames s
-- | _, _ => ""

-- def ConForester_Ty : List String → preTy → List preArg → String
-- | _, preUU, _ => "\\Set"
-- | topnames, preEL t, _ =>
--     ConForester_Tm topnames t
-- | topnames, preEQ s t, _ =>
--     ConForester_Tm topnames s ++ " = " ++ ConForester_Tm topnames t
-- | topnames, prePI _ Y, preAnon TT ::trest =>
--     ConForester_Ty topnames TT [] ++ " \\to " ++ ConForester_Ty (""::topnames) Y trest
-- | topnames, prePI _ Y, preExpl s TT ::trest =>
--     "(" ++ identFormat s ++ " : " ++ ConForester_Ty topnames TT [] ++ ") \\to " ++ ConForester_Ty (s::topnames) Y trest
-- | _, _, _ => ""


-- def ConForester_Con : preCon → List String
-- | [] => []
-- | [X] =>
--     [identFormat s ++ " \\colon " ++ ConForester_Ty [] X tt]
-- | ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
--     ConForester_Con ⟨XS,ss,tts⟩ ++
--     [identFormat s ++ " \\colon " ++ ConForester_Ty ss X tt]
-- | _ => []


def ConForester (𝔊 : GATdata) (G : String) : List String :=
["\\taxon{Definition}","","\\import{index}","\\title{#{\\mathfrak{" ++ G ++ "}}}"]
++ ["\\p{The GAT #{\\GAT{" ++ G ++ "}} is given by the signature"]
++ ["\\<html:ul>[style]{list-style-type:'▷  ';list-style-position: inside;}{","\\<html:li>[style]{list-style-type:'◇';list-style-position: outside;}{}"]
++ List.map liFormat (List.map (λ A => collapseFor (ConForester_Ty A)) (List.reverse 𝔊.con))
++ ["}","}"]
-- | ⟨[],_,_⟩ => []
-- | ⟨[X],[s],[(tt,_)]⟩ =>
--     [s ++ " : " ++ ConForester_Ty [] X tt]
-- | ⟨X::XS,s::ss,(tt,_)::tts⟩ =>
--     ConForester_Con ⟨XS,ss,tts⟩ ++
--     [s ++ " : " ++ ConForester_Ty ss X tt]
-- | _ => []
