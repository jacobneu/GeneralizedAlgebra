import GeneralizedAlgebra.helper


open Nat

def parenFor sl := paren' " " sl [" "]
def collapseFor := String.intercalate " "

inductive psExp : Type where
| psLit : String → psExp
| psL : List psExp → psExp -- be lazy about parens on the first
| psR :  List psExp → psExp -- be lazy about parens on the last
| psPar : List psExp → psExp -- be strict about parens
| psNopar : List psExp → psExp -- don't require parens
| psDep : List (String × psExp) → psExp → psExp
| psDepI : List (String × psExp) → psExp → psExp
| psDecorate : psExp → (String → String) → psExp
open psExp

def psExp.reprPrec : psExp → Nat → String
| psLit s, _ => "psLit(" ++ s ++ ")"
| psL xs, succ i => "psL [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| psR xs, succ i => "psR [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| psPar xs, succ i => "psPar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| psDep tel body, succ i => "psDep [" ++ String.intercalate "," (List.map (λ (s,t) => "(" ++ s ++ "," ++ reprPrec t i ++ ")") tel) ++ "] (" ++ reprPrec body i ++ ")"
| psDepI tel body, succ i => "psDepI [" ++ String.intercalate "," (List.map (λ (s,t) => "(" ++ s ++ "," ++ reprPrec t i ++ ")") tel) ++ "] (" ++ reprPrec body i ++ ")"
| psDecorate t _, succ i => "psDecorate (" ++ reprPrec t i ++ ") _"
| psNopar xs, succ i => "psNopar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| _ , 0 => "ZERO"

instance : Repr psExp where
  reprPrec := λ t _ => psExp.reprPrec t 100000



mutual
def psExp.toStringParen : Nat → psExp → String
| _, psLit s => s
| succ n, psR [x] => psExp.toString_core n x
| succ n, psPar [x] => psExp.toString_core n x
| succ n, psNopar [x] => psExp.toString_core n x
| succ n, psL [x] => psExp.toString_core n x
| succ n, psDecorate x f => f (psExp.toStringParen n x)
| _, psR [] => ""
| _, psPar [] => ""
| _, psNopar [] => ""
| _, psL [] => ""
| succ n, z => "(" ++ psExp.toString_core n z ++ ")"
| 0,_ => ""


def groupTel : Nat → List (String × psExp) → List String × String × List (String × psExp)
| _, [] => ([],"",[])
| n, [(i,tt)] => ([i],psExp.toString_core n tt,[])
| n, (i,tt)::(i',tt')::res =>
    let tts := psExp.toString_core n tt
    let tts' := psExp.toString_core n tt'
    if tts = tts'
    then
      let (others,_,remainder) := groupTel n ((i',tt')::res)
      (i::others,tts,remainder)
    else ([i],tts,(i',tt')::res)

def psExp.toString_core : Nat → psExp → String
| _, psLit s => s
| succ n, psL (psL fst :: rest) =>
    psExp.toString_core n (psL fst) ++ " " ++ String.intercalate " " (List.map (psExp.toStringParen n) rest)
| succ n, psL xs => String.intercalate " " (List.map (psExp.toStringParen n) xs)
| succ n, psR [psR xs] => psExp.toString_core n (psR xs)
| succ n, psR [x] => psExp.toStringParen n x
| succ n, psR (x :: xs) => psExp.toStringParen n x ++ " " ++ psExp.toString_core n (psR xs)
| _, psR [] => ""
| succ n, psPar xs => String.intercalate " " (List.map (psExp.toStringParen n) xs)
| succ n, psNopar xs => String.intercalate " " (List.map (psExp.toString_core n) xs)
| succ n, psDep [] body => match body with
    | psDep _ _ => psExp.toString_core n body
    | _ =>  " → " ++ psExp.toString_core n body
| succ n, psDep tel body =>
    let (is,tts,remainder) := groupTel (succ n) tel
    "(" ++ String.intercalate " " is ++ " : " ++ tts ++ ")" ++ psExp.toString_core n (psDep remainder body)
| succ n, psDepI tel body =>
    let (is,tts,remainder) := groupTel (succ n) tel
    "{" ++ String.intercalate " " is ++ " : " ++ tts ++ "}" ++ psExp.toString_core n (psDep remainder body)
| succ n, psDecorate tt f => f (psExp.toString_core n tt)
| 0, _ => ""
end

def psExp.strictify : psExp → psExp
| psNopar xs => psPar xs
| z => z

def psExp.toString : psExp → String := psExp.toString_core 1000000
