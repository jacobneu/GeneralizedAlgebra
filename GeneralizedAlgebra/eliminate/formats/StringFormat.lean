import GeneralizedAlgebra.helper


open Nat ArgMarker'

inductive sfDecor where
| sfId : sfDecor
| sfDalg : sfDecor
| sfHom : sfDecor
| sfSect : sfDecor
| sfZero : sfDecor
| sfOne : sfDecor
open sfDecor

inductive sfExp : Type where
-- | sfLit : String → sfExp
| sfIdentDec : String → sfDecor → sfExp
| sfDec : sfExp → sfDecor → sfExp
| sfL : List sfExp → sfExp -- be lazy about parens on the first
| sfR :  List sfExp → sfExp -- be lazy about parens on the last
| sfPar : List sfExp → sfExp -- be strict about parens
| sfNopar : List sfExp → sfExp -- don't require parens
| sfDep : List (ArgMarker' sfExp × sfExp) → sfExp → sfExp
| sfSet : sfExp
| sfEq : sfExp → sfExp → sfExp
| sfArr : sfExp → sfExp → sfExp
| sfTop : sfExp
open sfExp

def sfIdent s := sfIdentDec s sfId

def sfDecor.reprPrec : sfDecor → Nat → String
| sfDalg,_ => "sfDalg"
| sfHom,_ => "sfHom"
| sfSect,_ => "sfSect"
| sfZero,_ => "sfZero"
| sfOne,_ => "sfOne"
| sfId,_ => "sfId"

def sfExp.reprPrec : sfExp → Nat → String
| sfL xs, succ i => "sfL [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfR xs, succ i => "sfR [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfPar xs, succ i => "sfPar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfDep tel body, succ i => "sfDep [" ++ String.intercalate "," (List.map (λ (os,t) => @ArgMarker'.toString sfExp ⟨(sfExp.reprPrec · i)⟩ os (t.reprPrec i)) tel) ++ "] (" ++ reprPrec body i ++ ")"
| sfIdentDec s z, succ i => "sfIdentDec (" ++ s ++ ") " ++ z.reprPrec i
| sfDec s z, succ i => "sfDec (" ++ s.reprPrec i ++ ") " ++ z.reprPrec i
| sfNopar xs, succ i => "sfNopar [" ++ String.intercalate "," (List.map (λ t => reprPrec t i) xs) ++ "]"
| sfSet,_ => "sfSet"
| sfTop,_ => "sfTop"
| sfEq s1 s2,succ i => "sfEq (" ++ s1.reprPrec i ++ ") (" ++ s2.reprPrec i ++ ")"
| sfArr s1 s2,succ i => "sfArr (" ++ s1.reprPrec i ++ ") (" ++ s2.reprPrec i ++ ")"
| _ , 0 => "ZERO"

instance : Repr sfExp where
  reprPrec := λ t _ => sfExp.reprPrec t 100000

def mkSfArgMark (a : ArgMarker) (dec := sfId) : ArgMarker' sfExp := match a with
| Anon => Anon
| Impl s => Impl (sfIdentDec s dec)
| Expl s => Expl (sfIdentDec s dec)

def argDec (dec : sfDecor) : ArgMarker' sfExp → ArgMarker' sfExp
| Anon => Anon
| Impl (sfIdentDec s sfId) => Impl (sfIdentDec s dec)
| Expl (sfIdentDec s sfId) => Expl (sfIdentDec s dec)
| Expl s => Expl (sfDec s dec)
| Impl s => Impl (sfDec s dec)


structure StringFormat where
    (parenFor : List String → String)
    (collapseFor : List String → String)
    (decorate : String → sfDecor → String)
    (set : String)
    (eq : String)
    (arr : String)
    (top : String)
    (colon : String)
    (openCurly : String)
    (closeCurly : String)

def StringFormat.dalgFn (SF : StringFormat) s := SF.decorate s sfDalg
def StringFormat.oneFn (SF : StringFormat) s := SF.decorate s sfOne
def StringFormat.zeroFn (SF : StringFormat) s := SF.decorate s sfZero
def StringFormat.sectFn (SF : StringFormat) s := SF.decorate s sfSect
def StringFormat.homFn (SF : StringFormat) s := SF.decorate s sfHom


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
variable (SF : StringFormat)

def sfExp.toStringParen : Nat → sfExp → String
| _, sfIdentDec s dec => SF.decorate s dec
| succ n, sfDec s dec => SF.decorate (s.toString_core n) dec
| succ n, sfR [x] => sfExp.toString_core n x
| succ n, sfPar [x] => sfExp.toString_core n x
| succ n, sfNopar [x] => sfExp.toString_core n x
| succ n, sfL [x] => sfExp.toString_core n x
-- | succ n, sfDecorate x f => f (sfExp.toStringParen n x)
| _, sfR [] => ""
| _, sfPar [] => ""
| _, sfNopar [] => ""
| _, sfL [] => ""
| succ n, z => "(" ++ sfExp.toString_core n z ++ ")"
| 0,_ => ""


def closeArg (tts :  String) : Bool → String
| true => SF.collapseFor ["",SF.colon,tts] ++ ")"
| false => SF.collapseFor ["",SF.colon,tts] ++ SF.closeCurly
def openArg (s :  String) : Bool → String
| true => "(" ++ s
| false => SF.openCurly ++ s

def sfDepToString_core : Nat → String → Bool → List (ArgMarker' sfExp × sfExp) → String
-- match (b,tel) with
| _, tts, currentExpl, [] => closeArg tts currentExpl
| succ n, tts, currentExpl, (Impl s,tt')::rest =>
    let tts' := tt'.toString_core n
    let currentArg := match (currentExpl,tts == tts') with
        | (false, true) => SF.collapseFor ["",s.toString_core n]
        | _ => closeArg tts currentExpl ++ openArg (s.toString_core n) false
    currentArg ++ sfDepToString_core n tts' false rest
| succ n, tts, currentExpl, (Expl s,tt')::rest =>
    let tts' := tt'.toString_core n
    let currentArg := match (currentExpl,tts == tts') with
        | (true, true) => SF.collapseFor ["",s.toString_core n]
        | _ => closeArg tts currentExpl ++ openArg (s.toString_core n) true
    currentArg ++ sfDepToString_core n tts' true rest
| succ n, tts, currentExpl, tel => SF.collapseFor [closeArg tts currentExpl,SF.arr,sfDepToString n tel]
| 0, _, _,_ => ""

def sfDepToString : Nat → List (ArgMarker' sfExp × sfExp) → String
| succ n, [(Anon,tt)] => tt.toString_core n
| succ n, (Anon,tt)::rest => SF.collapseFor [tt.toString_core n,SF.arr,sfDepToString n rest]
| succ n, (Impl s,tt)::rest => openArg (s.toString_core n) false ++ sfDepToString_core n (tt.toString_core n) false rest
| succ n, (Expl s,tt)::rest => openArg (s.toString_core n) true ++ sfDepToString_core n (tt.toString_core n) true rest
| _,_ => ""


def sfExp.toString_core : Nat → sfExp → String
| 0,_ => ""
| _, sfIdentDec s z => SF.decorate s z
| succ n, sfDec s z => SF.decorate (s.toString_core n) z
| succ n, sfL (sfL fst :: rest) =>
    SF.collapseFor $ ((sfL fst).toString_core n) :: (List.map (sfExp.toStringParen n) rest)
| succ n, sfL xs => SF.collapseFor (List.map (sfExp.toStringParen n) xs)
| succ n, sfR [sfR xs] => (sfR xs).toString_core n
| succ n, sfR [x] => x.toStringParen n
| succ n, sfR (x :: xs) => SF.collapseFor [x.toStringParen n, (sfR xs).toString_core n]
| _, sfR [] => ""
| succ n, sfPar xs => SF.collapseFor (List.map (sfExp.toStringParen n) xs)
| succ n, sfNopar xs => SF.collapseFor (List.map (sfExp.toString_core n) xs)
| succ n, sfDep tel body => match telCmb (sfDep tel body) with
    | sfDep tel' body' => SF.collapseFor [sfDepToString n tel',SF.arr,sfExp.toString_core n body']
    | _ => SF.collapseFor [sfDepToString n tel,SF.arr,body.toString_core n]
-- | succ n, sfDecorate tt f => f (tt.toString_core n)
| _,sfSet => SF.set
| _,sfTop => SF.top
|succ n, sfEq s1 s2 =>
    let s1' := match s1 with
        | sfNopar xs => SF.collapseFor (List.map (sfExp.toStringParen n) xs)
        | _ => s1.toString_core n
    let s2' := match s2 with
        | sfNopar xs => SF.collapseFor (List.map (sfExp.toStringParen n) xs)
        | _ => s2.toString_core n
    SF.collapseFor [s1',SF.eq,s2']
| succ n, sfArr s1 s2 => SF.collapseFor [s1.toString_core n,SF.arr,s2.toString_core n]
end
def sfExp.toString (SF : StringFormat) (input : sfExp) : String := sfExp.toString_core SF 10000 input

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


def getNameAM {m}[Monad m] : ArgMarker → StateT Nat m (ArgMarker' sfExp × String × Bool)
| Expl s => return (Expl (sfIdent s),s,true)
| Impl s => return (Impl (sfIdent s),s,false)
| Anon => do
  let x ← get
  set $ succ x
  let vf := varFormat x
  return (Expl (sfIdent vf),vf,true)

-- def getNameSF {m}[Monad m] : ArgMarker' sfExp → StateT Nat m (ArgMarker' sfExp × String × Bool)
-- | Expl s => return (Expl (sfIdent s),s,true)
-- | Impl s => return (Impl (sfIdent s),s,false)
-- | Anon => do
--   let x ← get
--   set $ succ x
--   let vf := varFormat x
--   return (Expl (sfIdent vf),vf,true)

def mkReplaceVF reps s :=
    (List.foldl (λ (s',n) rep => (String.replace s' (varFormat n) rep,succ n)) (s,0) reps).1

def mkReplace reps s :=
    List.foldl (λ s' (tgt,rep) => String.replace s' tgt rep) s reps


notation i " /w " ll => List.map (mkReplace ll) i
notation s " ⧸ " i => (varFormat i,s)


def OuterToString (SF : StringFormat) : (String × sfExp) → String
| (s, pe) => SF.collapseFor [s, SF.colon, pe.toString SF]
def OuterToStringDec (SF : StringFormat) (dec : sfDecor) : (String × sfExp) → String
| (s, pe) => SF.collapseFor [SF.decorate s dec, SF.colon, pe.toString SF]
