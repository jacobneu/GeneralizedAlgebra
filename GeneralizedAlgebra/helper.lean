import Lean.Syntax
open Nat

def stripFirstParen : List Char → Option (List Char)
| '('::xs => some xs
| _ => none
def stripLastParen : List Char → Option (List Char)
| [] => none
| [')'] => some []
| x::xs => do
  let stripped <- stripLastParen xs
  return x::stripped


def stripOuterParen (s : String) : Option (List Char) := do
  let charList := String.toList s
  stripFirstParen charList >>= stripLastParen


def parenCounter : Option Nat → Char → Option Nat
| some n, '(' => some $ succ n
| some (succ n), ')' => some n
| some 0, ')' => none
| o, _ => o

def parensUnnecessary (s : String) : Bool :=
   Option.isSome (stripOuterParen s >>= List.foldl parenCounter (some 0))
|| (Option.isNone $ List.find? Char.isWhitespace $ String.toList s)

def mkParen (s:String):String := if parensUnnecessary s then s else "("++s++")"

def replaceAllWithSpace (asSpace : List String) (s : String) :String :=
  List.foldl (λ as curr => curr.replace as " ") s asSpace

def paren' (sep : String) (sl : List String) (asSpace : List String := []): String :=
  if parensUnnecessary (String.intercalate " " (List.map (replaceAllWithSpace asSpace) sl))
  then String.intercalate sep sl
  else "("++ String.intercalate sep sl ++")"


def List.zipWithSnd {α}{β}{γ} (g : Option α → β → γ) : List α → List β → List γ
| _, [] => []
| [], y::ys => g none y :: List.zipWithSnd g [] ys
| x::xs, y::ys => g (some x) y :: List.zipWithSnd g xs ys

inductive ArgMarker' (identType : Type) : Type where
| Anon : ArgMarker' identType
| Expl : identType → ArgMarker' identType
| Impl : identType → ArgMarker' identType
open ArgMarker'

def ArgMarker := ArgMarker' String

def extractIdent? {identType : Type} : ArgMarker' identType → Option identType
| Anon => none
| Impl s => some s
| Expl s => some s

def ArgMarker'.toString {identType : Type} [ts : ToString identType]: ArgMarker' identType → String → String
| Anon, tts => tts
| Expl s, tts => "(" ++ ts.toString s ++ " : " ++ tts ++ ")"
| Impl s, tts => "{" ++ ts.toString s ++ " : " ++ tts ++ "}"

def ArgMarker.toString : ArgMarker → String → String := ArgMarker'.toString

def ArgMarker.map (f : String → String) : ArgMarker → ArgMarker
| Anon => Anon
| Expl s => Expl (f s)
| Impl s => Impl (f s)

def ArgMarker.getName : ArgMarker → String
| Anon => "_"
| Expl s => s
| Impl s => s
