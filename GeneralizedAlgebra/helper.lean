
open Nat

def stringCons := @List.cons String
def stringNil  := @List.nil String
def stringPure := @List.pure String


def snoc (L : List String) x := L ++ [x]

def filterNilStr := List.filter (Bool.not ∘ String.isEmpty)

def mappartial {α β} (f : α → Option β) : List α → List β
| [] => []
| x::xs => match f x with
  | some y => y::mappartial f xs
  | none => mappartial f xs

def mk2 (x:Con) (y:List String):= (x,y)
def mk3 {α : Type} (x:Con) (y:List String) (z : α) := (x,y,z)


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


def parenX (s:String):String :=
  if String.isNat (String.drop s 2) then s else "("++s++")"


def nth {α : Type}: Nat → List α → Option α
| _, [] => none
| 0, x::_ => return x
| succ n, _::xs => nth n xs

def nthBackwards (n:Nat) (L : List Nat) : Option Nat := nth n (List.reverse L)

def twoRepr (n : Nat) : String :=
  if n<10 then "0"++ Nat.repr n else
  Nat.repr n
def threeRepr (n : Nat) : String :=
  if n<10 then "00"++ Nat.repr n else
  if n<100 then "0"++ Nat.repr n else
  Nat.repr n

def collapse : List String → String
| [] => ""
| [x] => x
| x::L => "(" ++  List.foldl (λ s s' => s ++ "," ++ s' ) x L ++   ")"
