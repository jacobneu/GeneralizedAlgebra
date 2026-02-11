import GeneralizedAlgebra.signature
-- import Lean

-- open Lean Elab Meta
open Nat Except
open preTy preTm

mutual

inductive wellTy : preCon → preTy → Type where
| wellUU : ∀ {Γ : preCon}, wellTy Γ preUU
| wellWkTy : ∀ {Γ : preCon} {A : preTy} {B : preTy}, wellTy Γ A → wellTy (B :: Γ) (preWkTy A)
| wellEL : ∀ {Γ : preCon} {X : preTm}, wellTm Γ preUU X → wellTy Γ (preEL X)
| wellPI : ∀ {Γ : preCon} {X : preTm} {Y : preTy}, wellTm Γ preUU X → wellTy (preEL X :: Γ) Y → wellTy Γ (prePI X Y)

inductive wellTm : preCon → preTy → preTm → Type where
| wellZero : ∀ {Γ : preCon}{A : preTy}, wellTy Γ A → wellTm (A :: Γ) (preWkTy A) (preVAR 0)
| wellWkTm : ∀ {Γ : preCon}{A B : preTy}{t : preTm}, wellTm Γ A t → wellTm (B :: Γ) (preWkTy A) (preWkTm t)
| wellAPP : ∀ {Γ : preCon} {X : preTm} {Y : preTy} {f s : preTm}, wellTm Γ (prePI X Y) f → wellTm Γ (preEL X) s → wellTm Γ (substTy 0 s Y) (preAPP f s)


end

inductive wellCon : preCon → Type where
| wellEmpty : wellCon []
| wellCons : ∀ {Γ : preCon}{A : preTy}, wellTy Γ A → wellCon Γ → wellCon (A :: Γ)

open wellTy wellTm wellCon




-- mutual

-- def synthTy : preTy → Con → Ty
-- | preUU , _ => UU
-- |


-- end


-- structure GAT extends GATdata where
--   (typedCon : Except String Con)
--   (elim : (P : indData) → P.Con_D con)


-- def getSuccess {α} : Except String α → Option α
-- | Except.ok x => some x
-- | Except.error _ => none
-- def getError {α} : Except String α → Option String
-- | Except.ok _ => none
-- | Except.error s => some s

def test0 := [
  preEL (preVAR 0),
  preUU]

def thm0 : wellCon test0 :=
by
    apply wellCons
    apply wellEL
    apply wellZero
    apply wellUU
    apply wellCons
    apply wellUU
    apply wellEmpty

def test1 := [
  prePI (preVAR 1) preUU,
  preEL (preVAR 0),
  preUU]

def thm1 : wellCon test1 :=
by
    apply wellCons
    apply wellPI
    apply @wellWkTm [preUU] preUU _ (preVAR 0)
    apply wellZero
    apply wellUU
    apply wellUU
    apply thm0

def test2 := [
  -- prePI (preVAR 1) (preEL $ preAPP (preVAR 1) (preVAR 0)) ,
  preEL $ preAPP (preVAR 0) (preVAR 1),
  prePI (preVAR 1) preUU,
  preEL (preVAR 0),
  preUU]

def thm2 : wellCon test2 :=
by
    apply wellCons
    apply wellEL
    apply @wellAPP _ (preVAR 2) preUU _ _
    apply wellZero
    apply wellPI
    apply @wellWkTm _ preUU (preEL (preVAR 0)) (preVAR 0)
    apply wellZero
    apply wellUU
    apply wellUU
    apply @wellWkTm _ (preEL (preVAR 1)) _ (preVAR 0)
    apply wellZero
    apply wellEL
    apply wellZero
    apply wellUU
    exact thm1

def test3 := [
  prePI (preVAR 2) (preEL $ preAPP (preVAR 1) (preVAR 0)),
  prePI (preVAR 1) preUU,
  preEL (preVAR 0),
  preUU]

#check wellWkTm
#check wellAPP

def thm3 : wellCon test3 :=
by
  apply wellCons
  apply wellPI
  apply @wellWkTm _ preUU _ (preVAR 1)
  apply @wellWkTm _ preUU _ (preVAR 0)
  apply wellZero
  apply wellUU
  apply wellEL
  apply @wellAPP _ (preVAR 3) preUU _ _
  apply @wellWkTm _ (prePI (preVAR 2) preUU) _ (preVAR 0)
  apply wellZero
  apply wellPI
  apply @wellWkTm _ preUU _ (preVAR 0)
  apply wellZero
  apply wellUU
  apply wellUU
  apply wellZero
  apply wellEL
  apply @wellWkTm _ preUU _ (preVAR 1)
  apply @wellWkTm _ preUU _ (preVAR 0)
  apply wellZero
  apply wellUU
  apply thm1
-- #eval getError $ compileCon test1
-- #reduce compileCon test1

-- #reduce getSuccess $ do
--     let Γ ← compileCon test1
--     -- compileTm Γ (litTy UU) (preAPP (preVAR 0) (preVAR 1))
--     compileTm Γ (probPI QTm QTy) (preVAR 0)


def test := [
  prePI (preVAR 2) (preEL $ preAPP (preVAR 1) (preVAR 0)) ,
  -- preEL $ preAPP (preVAR 0) (preVAR 1),
  prePI (preVAR 1) (prePI (preVAR 2) preUU),
  preEL (preVAR 0),
  preUU]

-- #reduce getError $ do
--     let Γ ← compileCon test
--     -- compileTm Γ (litTy UU) (preAPP (preVAR 0) (preVAR 1))
--     compileTm Γ (litTy UU) (preAPP (preAPP (preVAR 0) (preVAR 1)) (preVAR 1))

-- #reduce compileCon test
-- #eval getError $ compileCon test
