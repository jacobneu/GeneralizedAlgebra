import GeneralizedAlgebra.signature
import GeneralizedAlgebra.eliminate.formats.PseudoAgda

open Nat
open preTy preTm

namespace SFparam

variable (SF : StringFormat)

def wkStr (s : String) : String :=
match s.toNat? with
| (some n) => Nat.repr (succ n)
| _ => s ++ SF.conWk

def ConStr_Tm : preTm → String
| preAPP (preAPP f t1) t2 =>   SF.collapseFor [ConStr_Tm (preAPP f t1),SF.conApplic, (mkParen (ConStr_Tm t2))] -- mkParen (ConStr_Tm f) ++ " @ " ++ mkParen (ConStr_Tm t1) ++ " @ " ++ mkParen (ConStr_Tm t2)
| preAPP f t =>  SF.collapseFor [mkParen (ConStr_Tm f),SF.conApplic, (mkParen (ConStr_Tm t))]
| preVAR n => Nat.repr n
| preTRANSP eq y => SF.collapseFor [SF.conTransp, mkParen (ConStr_Tm eq), mkParen (ConStr_Tm y)]

def ConStr_Ty : preTy → String
| preUU => SF.conUU
| preEQ s t => SF.collapseFor [SF.conEq,mkParen (ConStr_Tm SF s),mkParen (ConStr_Tm SF t)]
| preEL X => SF.collapseFor [SF.conEl,ConStr_Tm SF X]
| prePI X Y => SF.conPi (mkParen (ConStr_Tm SF X)) (mkParen (ConStr_Ty Y))


-- def Con_Con_core : List preTy → List sfExp
-- | A :: augCon =>
-- do
--     let res ← Alg_Con_core augCon
--     let firstname ← AlgStr_Ty (augCon.map (λ (os',_) => sfIdent <$> os')) aT
--     return res ++ [(s,firstname)]
-- | [] => return []

def ConStr_Con_core (Γ : List preTy) : List String := (List.map (ConStr_Ty SF) Γ.reverse)

def ConStr_Con (Γ : List preTy) : String :=
  List.foldl (· ++ "\n" ++ ·) "" (List.map (SF.formatLine · sfDecor.sfId) $ ConStr_Con_core SF Γ)

end SFparam
    -- match Alg_Con_core AΓ' with
    --     | some ll =>  List.map (OuterToString SF) ll
    --     | none => []
open SFparam

instance : Repr preTm where
  reprPrec := λ t _ => ConStr_Tm pseudoAgda t
instance : Repr preTy where
  reprPrec := λ t _ => ConStr_Ty pseudoAgda t

def preConrepr : preCon → String :=
(List.foldr (λ x y => y ++ " ▷ " ++ x) "◇") ∘ (List.map (ConStr_Ty pseudoAgda))

instance : Repr preCon :=
⟨ λ 𝔊 _ => preConrepr 𝔊 ⟩

def printPreCon (Γ : preCon) (SF := pseudoAgda): IO Unit := do
  IO.println "◇"
  List.forM (List.reverse Γ) (λ t => IO.println $ SF.formatLine (ConStr_Ty SF t) sfDecor.sfId)

-- instance GATRepr : Repr GAT :=
-- ⟨ λ 𝔊 _ =>  preConrepr (𝔊.toGATdata.con) ⟩

instance GATdataRepr : Repr GATdata :=
⟨ λ 𝔊 _ =>  preConrepr (𝔊.con) ⟩
