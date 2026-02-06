import GeneralizedAlgebra.signature
-- import Lean

-- open Lean Elab Meta
open Nat Except
open preTy preTm

mutual
inductive Con : Type where
| EMPTY : Con
| EXTEND : Con → Ty → Con

inductive Ty : Type where
| UU : Ty
| EL : Tm → Ty
| PI : Tm → Ty → Ty

inductive Tm : Type where
| VAR : Nat → Tm
| APP : Tm → Ty → Tm → Tm → Tm

end
open Con Ty Tm

mutual
def Ty.repr : Ty → String
| UU => "U"
| EL X => "EL (" ++ (Tm.repr X) ++ ")"
| PI X Y => "Π (" ++ (Tm.repr X) ++ ") (" ++ (Ty.repr Y) ++ ")"

def Tm.repr : Tm → String
| VAR n => Nat.repr n
| APP _ _ f t => (Tm.repr f) ++ " @ " ++ (Tm.repr t)
end

mutual
def Tm.decEq (t t' : Tm) : Decidable (t = t') :=
  match t, t' with
  | VAR m , VAR n => match Nat.decEq m n with
      | isTrue h => isTrue (congrArg VAR h)
      | isFalse h => isFalse (fun h' => by injection h' with e; exact h e)
  | APP X Y f t, APP X' Y' f' t' =>
      match Tm.decEq X X', Ty.decEq Y Y', Tm.decEq f f', Tm.decEq t t' with
      | isTrue hX, isTrue hY, isTrue hf, isTrue ht =>
          isTrue $ congr (congr (congr (congrArg _ hX) hY) hf) ht
      | isFalse hX, _, _, _ => isFalse (fun h' => by injection h' with eX; exact hX eX)
      | _, isFalse hY, _, _ => isFalse (fun h' => by injection h' with eX eY; exact hY eY)
      | _, _, isFalse hf, _ => isFalse (fun h' => by injection h' with eX eY ef; exact hf ef)
      | _, _, _, isFalse ht => isFalse (fun h' => by injection h' with eX eY ef et; exact ht et)
  | APP _ _ _ _, VAR _ => isFalse (fun h => Tm.noConfusion h)
  | VAR _, APP _ _ _ _ => isFalse (fun h => Tm.noConfusion h)

def Ty.decEq (A B : Ty) : Decidable (A = B) :=
  match A, B with
  | UU , UU => isTrue rfl
  | UU , EL _ => isFalse (fun h => Ty.noConfusion h)
  | UU , PI _ _ => isFalse (fun h => Ty.noConfusion h)
  | EL _ , UU => isFalse (fun h => Ty.noConfusion h)
  | EL t , EL t' => match Tm.decEq t t' with
      | isTrue h => isTrue (congrArg EL h)
      | isFalse h => isFalse (fun h' => by injection h' with e; exact h e)
  | EL _ , PI _ _ => isFalse (fun h => Ty.noConfusion h)
  | PI _ _, UU => isFalse (fun h => Ty.noConfusion h)
  | PI _ _, EL _ => isFalse (fun h => Ty.noConfusion h)
  | PI X Y, PI X' Y' => match Tm.decEq X X', Ty.decEq Y Y' with
      | isTrue hX, isTrue hY => isTrue (congr (congrArg _ hX) hY)
      | isFalse hX, _ => isFalse (fun h' => by injection h' with e; exact hX e)
      | _ , isFalse hY => isFalse (fun h' => by injection h' with e e'; exact hY e')
end

instance : DecidableEq Tm := Tm.decEq
instance : DecidableEq Ty := Ty.decEq

mutual
inductive probTy : Type where
| litTy : Ty → probTy
| QTy : probTy
| probEL : probTm → probTy
| probPI : probTm → probTy → probTy

inductive probTm : Type where
| litTm : Tm → probTm
| QTm : probTm
| probVAR : probTm

end
open probTy probTm

mutual
def wkTy : Ty → Ty
| UU => UU
| PI X Y => PI (wkTm X) (wkTy Y)
| EL X => EL (wkTm X)
def wkTm : Tm → Tm
| VAR n => VAR (succ n)
| APP X Y f t => APP (wkTm X) (wkTy Y) (wkTm f) (wkTm t)
def unwkTy : Ty → Except String Ty
| UU => return UU
| PI X Y => do
    let X' ← unwkTm X
    let Y' ← unwkTy Y
    return PI X' Y'
| EL X => do
    let X' ← unwkTm X
    return EL X'
def unwkTm : Tm → Except String Tm
| VAR 0 => error "Tried to unweaken VAR 0"
| APP X Y f t => do
    let X' ← unwkTm X
    let Y' ← unwkTy Y
    let f' ← unwkTm f
    let t' ← unwkTm t
    return APP X' Y' f' t'
| VAR (succ n) => return VAR n

def punwkTy : probTy → Except String probTy
| litTy A => do
    let A' ← unwkTy A
    return litTy A'
| probPI pX pY => do
    let pX' ← punwkTm pX
    let pY' ← punwkTy pY
    return probPI pX' pY'
| probEL pX => do
    let pX' ← punwkTm pX
    return probEL pX'
| QTy => return QTy

def punwkTm : probTm → Except String probTm
| litTm X => do
    let X' ← unwkTm X
    return litTm X'
| probVAR => return probVAR
| QTm => return QTm
end

mutual
def redTy : probTy → probTy
| probEL pX => match redTm pX with
  | litTm X => litTy (EL X)
  | pX' => probEL pX'
| probPI pX pY => match redTm pX, redTy pY with
  | litTm X, litTy Y => litTy (PI X Y)
  | pX', pY' => probPI pX' pY'
| Z => Z

def redTm : probTm → probTm
| Z => Z
end

mutual
def matchesTy (pA : probTy) (B : Ty) : Except String Ty :=
  match redTy pA , B with
  | QTy, _ => return B
  | litTy A, _ => if A = B then return A else error $ "literal type `" ++ Ty.repr A ++ "` does not match `" ++ (Ty.repr B) ++ "`"
  | probPI pX pY, PI X Y => do
      let _ ← matchesTm pX X
      let _ ← matchesTy pY Y
      return (PI X Y)
  | probEL pX, EL X => do
      let _ ← matchesTm pX X
      return (EL X)
  | _, _ => error $ "Wildcard matchesTy"

def matchesTm (pX : probTm) (X : Tm) : Except String Tm :=
  match redTm pX, X with
  | QTm , _ => return X
  | litTm Z, _ => if Z = X then return X else error $ "literal term `" ++ Tm.repr Z ++ "` does not match `" ++ Tm.repr X ++ "`"
  | _ , _ => error $ "Wildcard matchesTm"
end

def extrPI (pPIXY : probTy) : Except String (probTm × probTy) := match redTy pPIXY with
  | litTy (PI X Y) => return (litTm X,litTy Y)
  | QTy =>  error $ "Wildcard extrPI QTy"
  | probPI pX pY => return (redTm pX, redTy pY)
  | _ =>  error $ "Wildcard extrPI"

def extrEL (pELX : probTy) : Except String probTm := match redTy pELX with
  | litTy (EL X) => return litTm X
  | QTy =>  error $ "Wildcard extrEL QTy"
  | probEL pX => return pX
  | _ =>  error $ "Wildcard extrEL"

def forceTm : probTm → Except String Tm
| litTm X => return X
| _ => error "Failed to extract Tm"
def forceTy : probTy → Except String Ty
| litTy A => return A
| _ => error "Failed to extract Ty"

mutual
def compileCon : preCon → Except String Con
| [] => return EMPTY
| A::AS => do
    let Γ ← compileCon AS
    let cA ← compileTy Γ A
    return EXTEND Γ cA

def compileTy : Con → preTy → Except String Ty
| _ , preUU => return UU
| Γ , preEL X => do
    let (cX,_) ← compileTm Γ (litTy UU) X
    return EL cX
| Γ , prePI X Y => do
    let (cX,_) ← compileTm Γ (litTy UU) X
    let cY ← compileTy (EXTEND Γ (EL cX)) Y
    return PI cX cY
| _ , _ => error $ "Wildcard compileTy"

def compileTm : Con → probTy → preTm → Except String (Tm × probTy)
| EXTEND _ A, pA , preVAR 0 => do
    let _ ← matchesTy pA A
    return (VAR 0, litTy (wkTy A))
| EXTEND Γ _, pA , preVAR (succ n) => do
  let pA' ← punwkTy pA
  match compileTm Γ pA' (preVAR n) with
  | ok (VAR k, A) => return (VAR (succ k), A)
  | error e =>  error $ "Wildcard EXTEND Γ _, pA, preVAR (succ n): error '" ++ e ++ "'"
  | _ =>  error $ "Wildcard EXTEND Γ _, pA, preVAR (succ n)"
| Γ , Yt, preAPP f t => do
    let (cf,pPIXY) ← compileTm Γ (probPI QTm QTy) f
    let (pX,pY) ← extrPI pPIXY
    -- let (ct,pELX) ← compileTm Γ (QTy) t
    let (ct,pELX) ← compileTm Γ (redTy (probEL pX)) t
    let pX' ← extrEL pELX
    let X ← forceTm (redTm pX')
    let Y ← forceTy (redTy pY)
    let _ ← matchesTy pELX (EL X)
    -- Check Yt
    return (APP X Y cf ct, Yt)
| _ , _ , _ =>  error $ "Wildcard compileTm"

end


structure GAT extends GATdata where
  (typedCon : Except String Con)
--   (elim : (P : indData) → P.Con_D con)


def getSuccess {α} : Except String α → Option α
| Except.ok x => some x
| Except.error _ => none
def getError {α} : Except String α → Option String
| Except.ok _ => none
| Except.error s => some s

def test1 := [
  -- prePI (preVAR 1) (preEL $ preAPP (preVAR 1) (preVAR 0)) ,
--   preEL $ preAPP (preVAR 0) (preVAR 1),
  prePI (preVAR 1) preUU,
  preEL (preVAR 0),
  preUU]
#eval getError $ compileCon test1
#reduce compileCon test1

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

#reduce getError $ do
    let Γ ← compileCon test
    -- compileTm Γ (litTy UU) (preAPP (preVAR 0) (preVAR 1))
    compileTm Γ (litTy UU) (preAPP (preAPP (preVAR 0) (preVAR 1)) (preVAR 1))

#reduce compileCon test
#eval getError $ compileCon test
