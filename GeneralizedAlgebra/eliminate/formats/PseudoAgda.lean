import GeneralizedAlgebra.helper


open Nat ArgMarker

def parenFor sl := paren' " " sl [" "]
def collapseFor := String.intercalate " "

inductive psExp : Type where
| psLit : String → psExp
| psL : List psExp → psExp -- be lazy about parens on the first
| psR :  List psExp → psExp -- be lazy about parens on the last
| psPar : List psExp → psExp -- be strict about parens
| psNopar : List psExp → psExp -- don't require parens
| psDep : List (ArgMarker × psExp) → psExp → psExp
-- | psDepI : List (String × psExp) → psExp → psExp
| psDecorate : psExp → (String → String) → psExp
open psExp


def psExp.reprPrec : psExp → Nat → String
| psLit s, _ => "psLit(" ++ s ++ ")"
| psL xs, succ i => "psL [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| psR xs, succ i => "psR [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| psPar xs, succ i => "psPar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| psDep tel body, succ i => "psDep [" ++ String.intercalate "," (List.map (λ (os,t) => os.toString (t.reprPrec i)) tel) ++ "] (" ++ reprPrec body i ++ ")"
| psDecorate t _, succ i => "psDecorate (" ++ reprPrec t i ++ ") _"
| psNopar xs, succ i => "psNopar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| _ , 0 => "ZERO"

instance : Repr psExp where
  reprPrec := λ t _ => psExp.reprPrec t 100000



def telCmb : psExp → psExp
| psDep tel body =>
    match telCmb body with
    | psDep tel' body' => psDep (tel++tel') body'
    | body' => psDep tel body'
-- | psL ll => psL $ List.map telCmb ll
-- | psR ll => psR $ List.map telCmb ll
-- | psPar ll => psPar $ List.map telCmb ll
-- | psNopar ll => psNopar $ List.map telCmb ll
-- | psDecorate x f => psDecorate (telCmb x) f
| z => z

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


def closeArg (tts :  String) : Bool → String
| true => " : " ++ tts ++ ")"
| false => " : " ++ tts ++ "}"
def openArg (s :  String) : Bool → String
| true => "(" ++ s
| false => "{" ++ s

def psDepToString_core : Nat → String → Bool → List (ArgMarker × psExp) → String
-- match (b,tel) with
| _, tts, currentExpl, [] => closeArg tts currentExpl
| succ n, tts, currentExpl, (Impl s,tt')::rest =>
    let tts' := tt'.toString_core n
    let currentArg := match (currentExpl,tts == tts') with
        | (false, true) => " " ++ s
        | _ => closeArg tts currentExpl ++ openArg s false
    currentArg ++ psDepToString_core n tts' false rest
| succ n, tts, currentExpl, (Expl s,tt')::rest =>
    let tts' := tt'.toString_core n
    let currentArg := match (currentExpl,tts == tts') with
        | (true, true) => " " ++ s
        | _ => closeArg tts currentExpl ++ openArg s true
    currentArg ++ psDepToString_core n tts' true rest
| succ n, tts, currentExpl, tel => closeArg tts currentExpl ++ " → " ++ psDepToString n tel
| 0, _, _,_ => ""

def psDepToString : Nat → List (ArgMarker × psExp) → String
| succ n, [(Anon,tt)] => tt.toString_core n
| succ n, (Anon,tt)::rest => tt.toString_core n ++ " → " ++ psDepToString n rest
| succ n, (Impl s,tt)::rest => openArg s false ++ psDepToString_core n (tt.toString_core n) false rest
| succ n, (Expl s,tt)::rest => openArg s true ++ psDepToString_core n (tt.toString_core n) true rest
| _,_ => ""


def psExp.toString_core : Nat → psExp → String
| 0,_ => ""
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
| succ n, psDep tel body => match telCmb (psDep tel body) with
    | psDep tel' body' =>  psDepToString n tel' ++ " → " ++ psExp.toString_core n body'
    | _ => psDepToString n tel ++ " → " ++ psExp.toString_core n body
| succ n, psDecorate tt f => f (psExp.toString_core n tt)

end
def psExp.toString (input : psExp) : String := psExp.toString_core 10000 input

def psExp.strictify : psExp → psExp
| psNopar xs => psPar xs
| z => z



def dalgFor sl := (parenFor sl) ++ "ᴰ"
def dalgFn s := s ++ "ᴰ"

def homFor sl := (parenFor sl) ++ "ᴹ"
def homFn s := s ++ "ᴹ"
def zeroFn s := s ++ "₀"
def oneFn s := s ++ "₁"


def OuterToString (f : String → String) : Option (String × Bool) → psExp → Option String
| some (s,true), pe => return collapseFor [f s, ":", pe.toString]
| _,_ => none

def threeFormat n := let ns := Nat.repr n
    match ns.length with
    | 1 => "00" ++ ns
    | 2 => "0" ++ ns
    | _ => ns
def varFormat n := "x✝" ++ threeFormat n ++ "✝"


def getName {m}[Monad m] : StateT Nat m String := do
  let x ← get
  set $ succ x
  return varFormat x


def getNameAM {m}[Monad m] : ArgMarker → StateT Nat m (ArgMarker × String × Bool)
| Expl s => return (Expl s,s,true)
| Impl s => return (Impl s,s,false)
| Anon => do
  let x ← get
  set $ succ x
  let vf := varFormat x
  return (Expl vf,vf,true)

def mkReplaceVF reps s :=
    (List.foldl (λ (s',n) rep => (String.replace s' (varFormat n) rep,succ n)) (s,0) reps).1

def mkReplace reps s :=
    List.foldl (λ s' (tgt,rep) => String.replace s' tgt rep) s reps


notation i " /w " ll => List.map (mkReplace ll) i
notation s " ⧸ " i => (varFormat i,s)
