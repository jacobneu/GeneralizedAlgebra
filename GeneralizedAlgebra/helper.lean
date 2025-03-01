
open Nat

def stringCons := @List.cons String
def stringNil  := @List.nil String
def stringPure := @List.pure String


def snoc (L : List String) x := L ++ [x]

def filterNilStr := List.filter (Bool.not ∘ String.isEmpty)

def mk2 (x:Con) (y:List String):= (x,y)
def mk3 (x:Con) (y:List String) (z : List String) := (x,y,z)

def paren (s:String):String :=
  if String.isNat s then s else "("++s++")"

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
