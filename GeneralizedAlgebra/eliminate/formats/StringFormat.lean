import GeneralizedAlgebra.helper


open Nat ArgMarker


inductive sfExp : Type where
| sfLit : String → sfExp
| sfL : List sfExp → sfExp -- be lazy about parens on the first
| sfR :  List sfExp → sfExp -- be lazy about parens on the last
| sfPar : List sfExp → sfExp -- be strict about parens
| sfNopar : List sfExp → sfExp -- don't require parens
| sfDep : List (ArgMarker × sfExp) → sfExp → sfExp
| sfDecorate : sfExp → (String → String) → sfExp
open sfExp


def sfExp.reprPrec : sfExp → Nat → String
| sfLit s, _ => "sfLit(" ++ s ++ ")"
| sfL xs, succ i => "sfL [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfR xs, succ i => "sfR [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfPar xs, succ i => "sfPar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfDep tel body, succ i => "sfDep [" ++ String.intercalate "," (List.map (λ (os,t) => os.toString (t.reprPrec i)) tel) ++ "] (" ++ reprPrec body i ++ ")"
| sfDecorate t _, succ i => "sfDecorate (" ++ reprPrec t i ++ ") _"
| sfNopar xs, succ i => "sfNopar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| _ , 0 => "ZERO"

instance : Repr sfExp where
  reprPrec := λ t _ => sfExp.reprPrec t 100000



def telCmb : sfExp → sfExp
| sfDep tel body =>
    match telCmb body with
    | sfDep tel' body' => sfDep (tel++tel') body'
    | body' => sfDep tel body'
-- | sfL ll => sfL $ List.map telCmb ll
-- | sfR ll => sfR $ List.map telCmb ll
-- | sfPar ll => sfPar $ List.map telCmb ll
-- | sfNopar ll => sfNopar $ List.map telCmb ll
-- | sfDecorate x f => sfDecorate (telCmb x) f
| z => z

mutual
def sfExp.toStringParen : Nat → sfExp → String
| _, sfLit s => s
| succ n, sfR [x] => sfExp.toString_core n x
| succ n, sfPar [x] => sfExp.toString_core n x
| succ n, sfNopar [x] => sfExp.toString_core n x
| succ n, sfL [x] => sfExp.toString_core n x
| succ n, sfDecorate x f => f (sfExp.toStringParen n x)
| _, sfR [] => ""
| _, sfPar [] => ""
| _, sfNopar [] => ""
| _, sfL [] => ""
| succ n, z => "(" ++ sfExp.toString_core n z ++ ")"
| 0,_ => ""


def closeArg (tts :  String) : Bool → String
| true => " : " ++ tts ++ ")"
| false => " : " ++ tts ++ "}"
def openArg (s :  String) : Bool → String
| true => "(" ++ s
| false => "{" ++ s

def sfDepToString_core : Nat → String → Bool → List (ArgMarker × sfExp) → String
-- match (b,tel) with
| _, tts, currentExpl, [] => closeArg tts currentExpl
| succ n, tts, currentExpl, (Impl s,tt')::rest =>
    let tts' := tt'.toString_core n
    let currentArg := match (currentExpl,tts == tts') with
        | (false, true) => " " ++ s
        | _ => closeArg tts currentExpl ++ openArg s false
    currentArg ++ sfDepToString_core n tts' false rest
| succ n, tts, currentExpl, (Expl s,tt')::rest =>
    let tts' := tt'.toString_core n
    let currentArg := match (currentExpl,tts == tts') with
        | (true, true) => " " ++ s
        | _ => closeArg tts currentExpl ++ openArg s true
    currentArg ++ sfDepToString_core n tts' true rest
| succ n, tts, currentExpl, tel => closeArg tts currentExpl ++ " → " ++ sfDepToString n tel
| 0, _, _,_ => ""

def sfDepToString : Nat → List (ArgMarker × sfExp) → String
| succ n, [(Anon,tt)] => tt.toString_core n
| succ n, (Anon,tt)::rest => tt.toString_core n ++ " → " ++ sfDepToString n rest
| succ n, (Impl s,tt)::rest => openArg s false ++ sfDepToString_core n (tt.toString_core n) false rest
| succ n, (Expl s,tt)::rest => openArg s true ++ sfDepToString_core n (tt.toString_core n) true rest
| _,_ => ""


def sfExp.toString_core : Nat → sfExp → String
| 0,_ => ""
| _, sfLit s => s
| succ n, sfL (sfL fst :: rest) =>
    sfExp.toString_core n (sfL fst) ++ " " ++ String.intercalate " " (List.map (sfExp.toStringParen n) rest)
| succ n, sfL xs => String.intercalate " " (List.map (sfExp.toStringParen n) xs)
| succ n, sfR [sfR xs] => sfExp.toString_core n (sfR xs)
| succ n, sfR [x] => sfExp.toStringParen n x
| succ n, sfR (x :: xs) => sfExp.toStringParen n x ++ " " ++ sfExp.toString_core n (sfR xs)
| _, sfR [] => ""
| succ n, sfPar xs => String.intercalate " " (List.map (sfExp.toStringParen n) xs)
| succ n, sfNopar xs => String.intercalate " " (List.map (sfExp.toString_core n) xs)
| succ n, sfDep tel body => match telCmb (sfDep tel body) with
    | sfDep tel' body' =>  sfDepToString n tel' ++ " → " ++ sfExp.toString_core n body'
    | _ => sfDepToString n tel ++ " → " ++ sfExp.toString_core n body
| succ n, sfDecorate tt f => f (sfExp.toString_core n tt)

end
def sfExp.toString (input : sfExp) : String := sfExp.toString_core 10000 input

def sfExp.strictify : sfExp → sfExp
| sfNopar xs => sfPar xs
| z => z



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



structure StringFormat where
    (parenFor : List String → String)
    (collapseFor : List String → String)
    (dalgFn : String → String)
    (homFn : String → String)
    (sectFn : String → String)
    (zeroFn : String → String)
    (oneFn : String → String)

def OuterToString (SF : StringFormat) (f : String → String) : Option (String × Bool) → sfExp → Option String
| some (s,true), pe => return SF.collapseFor [f s, ":", pe.toString]
| _,_ => none
