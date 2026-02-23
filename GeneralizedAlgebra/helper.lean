
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

def paren (s:String):String := if parensUnnecessary s then s else "("++s++")"
