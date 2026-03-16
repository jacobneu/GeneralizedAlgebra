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

def GAT.length : GAT → Nat
| ⟨⟨𝔊,_,_⟩,_⟩ => List.length 𝔊

def EMPTY : GAT := ⟨⟨[],[],[]⟩,wellEmpty⟩

def genTele_core (m n : Nat) : preTy → List preArg
| prePI X Y => preArg.preExpl ("Z_" ++ Nat.repr m ++ "_" ++ Nat.repr n) (preEL X) :: genTele_core m (succ n) Y
| _ => []

def genTele (m : Nat) (X : preTy) : List preArg × preTy := ⟨genTele_core m 0 X, X⟩

def EXTEND (𝔊 : GAT) (𝒜 : Ty 𝔊)
      (As : String := "Y_" ++ Nat.repr (GAT.length 𝔊))
      (newTele : List preArg × preTy := genTele (GAT.length 𝔊) 𝒜.1)
    : GAT :=
  ⟨⟨preEXTEND 𝔊.con 𝒜.1, As :: 𝔊.topnames,newTele :: 𝔊.telescopes⟩,wellCons 𝒜.2 𝔊.isWell⟩

def UU {𝔊 : GAT} : Ty 𝔊 := ⟨preUU,wellUU⟩
def EL {𝔊 : GAT} {wU : wellTy 𝔊.con preUU} (𝒳 : Tm 𝔊 ⟨preUU,wU⟩) : Ty 𝔊 :=
  ⟨preEL 𝒳.1,wellEL 𝒳.2⟩
def PI {𝔊 : GAT} {wU : wellTy 𝔊.con preUU} {newName : String} {newTele : List preArg × preTy}
  (𝒳 : Tm 𝔊 ⟨preUU,wU⟩) (𝒴 : Ty (EXTEND 𝔊 (EL 𝒳) newName newTele)) : Ty 𝔊 :=
  ⟨prePI 𝒳.1 𝒴.1,wellPI 𝒳.2 𝒴.2⟩

def EQ {𝔊 : GAT} {wU : wellTy 𝔊.con preUU} (𝒳 : Tm 𝔊 ⟨preUU,wU⟩) (s t : Tm 𝔊 (EL 𝒳)) : Ty 𝔊 :=
  ⟨preEQ s.1 t.1, wellEQ 𝒳.2 s.2 t.2⟩

def WKTY {𝔊 : GAT}(𝒜 : Ty 𝔊){ℬ : Ty 𝔊}
      (newName : String := "Y_" ++ Nat.repr (GAT.length 𝔊))
      (newTele : List preArg × preTy := genTele (GAT.length 𝔊) ℬ.1) : Ty (EXTEND 𝔊 ℬ newName newTele) :=
    ⟨preWkTy 𝒜.1,wellWkTy 𝒜.2⟩

def VARZERO {𝔊 : GAT}{𝒜 : Ty 𝔊}
      (newName : String := "Y_" ++ Nat.repr (GAT.length 𝔊))
      (newTele : List preArg × preTy := genTele (GAT.length 𝔊) 𝒜.1) : Tm (EXTEND 𝔊 𝒜) (WKTY 𝒜 newName newTele) :=
    ⟨preVAR 0,wellZero 𝒜.2⟩

def WKTM  {𝔊 : GAT}{𝒜 ℬ : Ty 𝔊}(t : Tm 𝔊 𝒜)
      (newName : String := "Y_" ++ Nat.repr (GAT.length 𝔊))
      (newTele : List preArg × preTy := genTele (GAT.length 𝔊) ℬ.1)
      : Tm (EXTEND 𝔊 ℬ newName newTele) (WKTY 𝒜 newName newTele) :=
    ⟨preWkTm t.1,wellWkTm t.2⟩

def SUBSTLAST {𝔊 : GAT} {𝒜 : Ty 𝔊} {newName : String} {newTele : List preArg × preTy} (𝒴 : Ty (EXTEND 𝔊 𝒜 newName newTele)) (t : Tm 𝔊 𝒜) : Ty 𝔊 :=
⟨substTy 0 t.1 𝒴.1,by
  match 𝒴 with
  | ⟨preUU,_⟩ => apply wellUU
  -- | ⟨preEL X,wellX⟩ => sorry
  | _ => sorry
⟩

-- def APP {𝔊 : GAT} {wU : wellTy 𝔊.con preUU} {𝒳 : Tm 𝔊 ⟨preUU,wU⟩}{Y : preTy}{wellY : wellTy (preEXTEND 𝔊.con (preEL 𝒳.1)) Y} {wellPi : wellTy 𝔊.con (prePI 𝒳.1 Y)} (f : Tm 𝔊 ⟨prePI 𝒳.1 Y,wellPi⟩) (t : Tm 𝔊 (EL 𝒳)) : Tm 𝔊 (SUBSTLAST ⟨Y,wellY⟩ t) :=
--   ⟨preAPP f.1 t.1,wellAPP f.2 t.2⟩

def test1 := EXTEND EMPTY UU
def test2 := EXTEND test1 (EL VARZERO)
def test3 := EXTEND test2 (EL $ WKTM VARZERO)
def test4 := EXTEND test3 (EQ (WKTM $ WKTM VARZERO) VARZERO (WKTM VARZERO))

def test4' := EXTEND test2 (@PI _ _ "x" ⟨[],preEL $ preVAR 1⟩ (WKTM VARZERO) UU)
-- def test4'' : Tm test4' UU := APP VARZERO _

-- 𝔑
def test5 := EXTEND test2 (PI (WKTM VARZERO) (EL (WKTM $ WKTM VARZERO)))

-- 𝔐𝔬𝔫
def test6 := EXTEND test2 (PI (WKTM VARZERO) (PI (WKTM $ WKTM VARZERO) (EL (WKTM $ WKTM $ WKTM VARZERO))))
-- def test7 := EXTEND test6 (PI (WKTM $ WKTM VARZERO) (EQ (WKTM $ WKTM $ WKTM VARZERO) (APP (APP (WKTM VARZERO) VARZERO)) VARZERO) VARZERO)

#reduce test6.con
