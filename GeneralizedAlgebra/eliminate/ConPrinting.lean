import GeneralizedAlgebra.typecheck

open Nat
open preTy preTm


def wkStr (s : String) : String :=
match s.toNat? with
| (some n) => Nat.repr (succ n)
| _ => s ++ "[wk]"

def preTmrepr : preTm → String
| preAPP (preAPP (preAPP (preAPP (preAPP f t1) t2) t3) t4) t5 => paren (preTmrepr f) ++ " @ " ++ paren (preTmrepr t1) ++ " @ " ++ paren (preTmrepr t2) ++ " @ " ++ paren (preTmrepr t3) ++ " @ " ++ paren (preTmrepr t4) ++ " @ " ++ paren (preTmrepr t5)
| preAPP (preAPP (preAPP (preAPP f t1) t2) t3) t4 => paren (preTmrepr f) ++ " @ " ++ paren (preTmrepr t1) ++ " @ " ++ paren (preTmrepr t2) ++ " @ " ++ paren (preTmrepr t3) ++ " @ " ++ paren (preTmrepr t4)
| preAPP (preAPP (preAPP f t1) t2) t3 => paren (preTmrepr f) ++ " @ " ++ paren (preTmrepr t1) ++ " @ " ++ paren (preTmrepr t2) ++ " @ " ++ paren (preTmrepr t3)
| preAPP (preAPP f t1) t2 => paren (preTmrepr f) ++ " @ " ++ paren (preTmrepr t1) ++ " @ " ++ paren (preTmrepr t2)
| preAPP f t =>   paren (preTmrepr f) ++ " @ " ++ paren (preTmrepr t)
| preVAR n => Nat.repr n
| preTRANSP eq y => "transp " ++ paren (preTmrepr eq) ++ " " ++ paren (preTmrepr y)

def preTyrepr : preTy → String
| preUU => "U"
| preEQ s t => "Eq " ++ paren (preTmrepr s)  ++ " " ++ paren (preTmrepr t)
| preEL X => "El " ++ paren (preTmrepr X)
| prePI X Y => "Π " ++ paren (preTmrepr X) ++ " " ++ paren (preTyrepr Y)



instance : Repr preTm where
  reprPrec := λ t _ => preTmrepr t
instance : Repr preTy where
  reprPrec := λ t _ => preTyrepr t

#eval List.foldr (λ x y => y ++ "-" ++ x) "x" ["a","b","c"]

def preConrepr : preCon → String :=
(List.foldr (λ x y => y ++ " ▷ " ++ x) "◇") ∘ (List.map preTyrepr)

instance : Repr preCon :=
⟨ λ 𝔊 _ => preConrepr 𝔊 ⟩

instance GATRepr : Repr GAT :=
⟨ λ 𝔊 _ =>  preConrepr (𝔊.toGATdata.con) ⟩

instance GATdataRepr : Repr GATdata :=
⟨ λ 𝔊 _ =>  preConrepr (𝔊.con) ⟩
