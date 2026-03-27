import GeneralizedAlgebra.typecheck

open Nat
open preTy preTm


def wkStr (s : String) : String :=
match s.toNat? with
| (some n) => Nat.repr (succ n)
| _ => s ++ "[wk]"

def preTmrepr : preTm → String
| preAPP (preAPP (preAPP (preAPP (preAPP f t1) t2) t3) t4) t5 => mkParen (preTmrepr f) ++ " @ " ++ mkParen (preTmrepr t1) ++ " @ " ++ mkParen (preTmrepr t2) ++ " @ " ++ mkParen (preTmrepr t3) ++ " @ " ++ mkParen (preTmrepr t4) ++ " @ " ++ mkParen (preTmrepr t5)
| preAPP (preAPP (preAPP (preAPP f t1) t2) t3) t4 => mkParen (preTmrepr f) ++ " @ " ++ mkParen (preTmrepr t1) ++ " @ " ++ mkParen (preTmrepr t2) ++ " @ " ++ mkParen (preTmrepr t3) ++ " @ " ++ mkParen (preTmrepr t4)
| preAPP (preAPP (preAPP f t1) t2) t3 => mkParen (preTmrepr f) ++ " @ " ++ mkParen (preTmrepr t1) ++ " @ " ++ mkParen (preTmrepr t2) ++ " @ " ++ mkParen (preTmrepr t3)
| preAPP (preAPP f t1) t2 => mkParen (preTmrepr f) ++ " @ " ++ mkParen (preTmrepr t1) ++ " @ " ++ mkParen (preTmrepr t2)
| preAPP f t =>   mkParen (preTmrepr f) ++ " @ " ++ mkParen (preTmrepr t)
| preVAR n => Nat.repr n
| preTRANSP eq y => "transp " ++ mkParen (preTmrepr eq) ++ " " ++ mkParen (preTmrepr y)
| holeTm => "?"

def preTyrepr : preTy → String
| preUU => "U"
| preEQ s t => "Eq " ++ mkParen (preTmrepr s)  ++ " " ++ mkParen (preTmrepr t)
| preEL X => "El " ++ mkParen (preTmrepr X)
| prePI X Y => "Π " ++ mkParen (preTmrepr X) ++ " " ++ mkParen (preTyrepr Y)



instance : Repr preTm where
  reprPrec := λ t _ => preTmrepr t
instance : Repr preTy where
  reprPrec := λ t _ => preTyrepr t

def preConrepr : preCon → String :=
(List.foldr (λ x y => y ++ " ▷ " ++ x) "◇") ∘ (List.map preTyrepr)

instance : Repr preCon :=
⟨ λ 𝔊 _ => preConrepr 𝔊 ⟩

instance GATRepr : Repr GAT :=
⟨ λ 𝔊 _ =>  preConrepr (𝔊.toGATdata.con) ⟩

instance GATdataRepr : Repr GATdata :=
⟨ λ 𝔊 _ =>  preConrepr (𝔊.con) ⟩
