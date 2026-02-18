import GeneralizedAlgebra.signature

open Nat Except
open preTy preTm

mutual

inductive wellTy : preCon → preTy → Type where
| wellUU : ∀ {Γ : preCon}, wellTy Γ preUU
| wellWkTy : ∀ {Γ : preCon} {A : preTy} {B : preTy}, wellTy Γ A → wellTy (B :: Γ) (preWkTy A)
| wellEL : ∀ {Γ : preCon} {X : preTm}, wellTm Γ preUU X → wellTy Γ (preEL X)
| wellPI : ∀ {Γ : preCon} {X : preTm} {Y : preTy}, wellTm Γ preUU X → wellTy (preEL X :: Γ) Y → wellTy Γ (prePI X Y)
| wellEQ : ∀ {Γ : preCon} {X s t : preTm}, wellTm Γ preUU X → wellTm Γ (preEL X) s → wellTm Γ (preEL X) t → wellTy Γ (preEQ s t)

inductive wellTm : preCon → preTy → preTm → Type where
| wellZero : ∀ {Γ : preCon}{A : preTy}, wellTy Γ A → wellTm (A :: Γ) (preWkTy A) (preVAR 0)
| wellWkTm : ∀ {Γ : preCon}{A B : preTy}{t : preTm}, wellTm Γ A t → wellTm (B :: Γ) (preWkTy A) (preWkTm t)
| wellAPP : ∀ {Γ : preCon} {X : preTm} {Y : preTy} {f s : preTm}, wellTm Γ (prePI X Y) f → wellTm Γ (preEL X) s → wellTm Γ (substTy 0 s Y) (preAPP f s)


end

inductive wellCon : preCon → Type where
| wellEmpty : wellCon []
| wellCons : ∀ {Γ : preCon}{A : preTy}, wellTy Γ A → wellCon Γ → wellCon (A :: Γ)

open wellTy wellTm wellCon


structure GAT extends GATdata where
  (isWell : wellCon con)

def Ty (𝔊 : GAT) : Type := Sigma (wellTy 𝔊.con)
def Tm (𝔊 : GAT) (𝒜 : Ty 𝔊) : Type := Sigma (wellTm 𝔊.con 𝒜.1)
