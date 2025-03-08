import GeneralizedAlgebra.helper

open Nat

mutual
  inductive preTm : Type where
  | preVAR : Nat → preTm
  | preAPP : preTm → preTm → preTm
  | preTRANSP : preTy → preTm → preTm → preTm

  inductive preTy : Type where
  | preUU : preTy
  | preEL : preTm → preTy
  | prePI : preTm → preTy → preTy
  | preEQ : preTm → preTm → preTm → preTy
end
open preTm preTy

-- Written backwards!
def preCon : Type := List preTy

mutual
  def preWkArrTy : preTy → Nat → preTy
  | preUU, _ => preUU
  | preEL X, a => preEL (preWkArrTm X a)
  | prePI X Y, a => prePI (preWkArrTm X a) (preWkArrTy Y (succ a))
  | preEQ A t t', a => preEQ (preWkArrTm A a) (preWkArrTm t a) (preWkArrTm t' a)
  def preWkArrTm : preTm → Nat → preTm
  | preVAR n, a => if n ≥ a then preVAR (succ n) else preVAR n
  | preAPP f t, a => preAPP (preWkArrTm f a) (preWkArrTm t a)
  | preTRANSP A eq t, a => preTRANSP (preWkArrTy A a) (preWkArrTm eq a) (preWkArrTm t a)
end

def preWkTy (A : preTy) : preTy := preWkArrTy A 0
def preWkTm (t : preTm) : preTm := preWkArrTm t 0

mutual
  def preSubstTy : preTy → preTm → preTy
  | preUU, _ => preUU
  | preEL X, z => preEL (preSubstTm X z)
  | prePI X Y, z => prePI (preSubstTm X z) (preSubstTy Y z)
  | preEQ A t t', z => preEQ (preSubstTm A z) (preSubstTm t z) (preSubstTm t' z)
  def preSubstTm : preTm → preTm → preTm
  | preVAR 0, z => z
  | preVAR (succ n), _ => preVAR n
  | preAPP f t, z => preAPP (preSubstTm f z) (preSubstTm t z)
  | preTRANSP A eq t, z => preTRANSP (preSubstTy A z) (preSubstTm eq z) (preSubstTm t z) -- ?
end


mutual
  inductive wfCon : preCon → Prop where
  | wfNil : wfCon []
  | wfCons : {Γ : preCon} → {A : preTy} → wfTy Γ A → (_ : wfCon Γ) → wfCon (A::Γ)

  inductive wfTy : preCon → preTy → Prop
  | wfWkTy : {Γ : preCon} → {A B : preTy} → wfTy Γ A → wfTy (B::Γ) (preWkTy A)
  | wfUU : {Γ : preCon} → wfTy Γ preUU
  | wfEL : {Γ : preCon} → {X : preTm} → wfTm Γ preUU X → wfTy Γ (preEL X)
  | wfPI : {Γ : preCon} → {X : preTm} → {Y : preTy} →
      wfTm Γ preUU X → wfTy (preEL X::Γ) Y → wfTy Γ (prePI X Y)
  | wfEQ : {Γ : preCon} → {X t t' : preTm} →
      wfTm Γ preUU X → wfTm Γ (preEL X) t → wfTm Γ (preEL X) t' → wfTy Γ (preEQ X t t')
  | wfSubstTy : {Γ : preCon} → {A B : preTy} → {t : preTm} →
      wfTy Γ B → wfTy (B::Γ) A → wfTm Γ B t → wfTy Γ (preSubstTy A t)

  inductive wfTm : preCon → preTy → preTm → Prop
  | wfVAR0 : {Γ : preCon} → {A : preTy} →
      wfTy Γ A → wfTm (A::Γ) (preWkTy A) (preVAR 0)
  | wfWkTm : {Γ : preCon} → {A B : preTy} → {t : preTm} →
      wfTm Γ A t → wfTy Γ B → wfTm (B::Γ) (preWkTy A) (preWkTm t)
  | wfAPP : {Γ : preCon} → {X : preTm} → {Y : preTy} → {f t : preTm} →
      wfTm Γ (prePI X Y) f → wfTm Γ (preEL X) t → wfTm Γ (preSubstTy Y t) (preAPP f t)
  | wfTRANSP : {Γ : preCon} → {X eq t t' z: preTm} → {Y : preTy} →
      {_ : wfTm Γ preUU X} → {_ : wfTy (preEL X::Γ) Y} →
      {_ : wfTm Γ (preEL X) t} → {_ : wfTm Γ (preEL X) t'} →
      wfTm Γ (preEQ X t t') eq →
      wfTm Γ (preSubstTy Y t) z →
      wfTm Γ (preSubstTy Y t') (preTRANSP Y eq z)
  | wfSubstTm : {Γ : preCon} → {A B : preTy} → {t t': preTm} →
      wfTm Γ B t → wfTm (B::Γ) A t' → wfTm Γ (preSubstTy A t) (preSubstTm t' t)
end

open wfCon wfTy wfTm

def Con : Type := { Γ : preCon // wfCon Γ }
def Ty (Γ : Con) : Type := { A : preTy // wfTy Γ.1 A}
def Tm (Γ : Con) (A : Ty Γ) : Type := { t : preTm // wfTm Γ.1 A.1 t}

def EMPTY : Con := ⟨[], wfNil⟩
def EXTEND (Γ : Con) (A : Ty Γ) : Con := ⟨ A.1 :: Γ.1 , wfCons A.2 Γ.2 ⟩

def UU {Γ : Con} : Ty Γ := ⟨ preUU , wfUU ⟩
def EL (Γ : Con) (X : Tm Γ UU) : Ty Γ := ⟨ preEL X.1 , wfEL X.2 ⟩
def PI (Γ : Con) (X : Tm Γ UU) (Y : Ty (EXTEND Γ (EL Γ X))) : Ty Γ :=
    ⟨ prePI X.1 Y.1 , wfPI X.2 Y.2 ⟩
def EQ (Γ : Con) (X : Tm Γ UU) (t t' : Tm Γ (EL Γ X)) : Ty Γ :=
    ⟨ preEQ X.1 t.1 t'.1 , wfEQ X.2 t.2 t'.2 ⟩

def wkTy (Γ : Con)(B : Ty Γ)(A : Ty Γ) : Ty (EXTEND Γ B) :=
    ⟨ preWkTy A.1 , wfWkTy A.2 ⟩
def substTy (Γ : Con)(B : Ty Γ)(A : Ty (EXTEND Γ B))(t : Tm Γ B) : Ty Γ :=
    ⟨ preSubstTy A.1 t.1, wfSubstTy B.2 A.2 t.2 ⟩
def APP (Γ : Con)(X : Tm Γ UU)(Y : Ty (EXTEND Γ (EL Γ X)))(f : Tm Γ (PI Γ X Y))(t : Tm Γ (EL Γ X)) : Tm Γ (substTy Γ (EL Γ X) Y t) :=
    ⟨ preAPP f.1 t.1, wfAPP f.2 t.2 ⟩

def ZERO (Γ : Con)(A : Ty Γ) : Tm (EXTEND Γ A) (wkTy Γ A A) :=
    ⟨ preVAR 0, wfVAR0 A.2 ⟩
def SUCC (Γ : Con)(B : Ty Γ)(A : Ty Γ) (t : Tm Γ A) : Tm (EXTEND Γ B) (wkTy Γ B A):=
    ⟨ preWkTm t.1 , wfWkTm t.2 B.2 ⟩

def len : Con → Nat := λ Γ => List.length Γ.1

-- #eval len $ EXTEND (EXTEND (EXTEND (EXTEND EMPTY UU) (PI ZERO (PI (SUCC ZERO) (EL $ SUCC $ SUCC $ ZERO)))) (EL $ SUCC $ ZERO)) (PI (SUCC $ SUCC $ ZERO) (EQ (SUCC $ SUCC $ SUCC $ ZERO) ZERO ZERO))


infixl:10 " ▷ " => EXTEND
notation "⋄" => EMPTY

-- def ONE := SUCC ZERO
def UUnil := @UU ⋄
def P := ⋄ ▷ UUnil
def Q := P ▷ EL P (ZERO ⋄ UUnil)
def P' := P ▷ PI P (ZERO ⋄ UUnil) (PI Q (SUCC P _ _ (ZERO ⋄ UUnil)) UU)
def Q' := P' ▷ EL _ (SUCC _ _ _ (ZERO _ _))
def Q'' := Q' ▷ EL _ (SUCC _ _ _ (SUCC _ _ _ (ZERO _ _)))
def P'' := P' ▷ PI _ (SUCC _ _ _ (ZERO _ _))
    (EL _ (APP Q' (SUCC P' _ _ (SUCC P _ _ (ZERO ⋄ _))) UU
        (APP Q' (SUCC _ _ _ (SUCC _ _ _ (ZERO _ _))) _
            _
            (ZERO _ _))
        (ZERO _ _)
      )
    )
    --

-- def x := @APP P''' (SUCC $ SUCC ZERO) UU (SUCC ZERO) (ZERO)
-- def Q := P'' ▷ PI (SUCC ZERO) (@EL P''' (@APP P''' _ _ _ _))
-- #reduce P'''

-- #eval len $
--     ⋄ ▷ UU ▷ PI ZERO UU
    -- ▷ PI (SUCC ZERO) (EL (@APP P''' (SUCC $ SUCC ZERO) UU (SUCC ZERO) (ZERO)))
    --▷ (PI (SUCC ZERO) (EL (APP (SUCC ZERO) _ )))
    -- ▷ (PI ZERO (PI (SUCC ZERO) (EL $ SUCC $ SUCC $ ZERO)))
    -- ▷ (PI (SUCC ZERO) (EQ (SUCC $ SUCC ZERO) (APP (SUCC $ ZERO) (APP _ _)) ZERO))
    -- ▷ (EL $ SUCC $ ZERO)
    -- ▷ (PI (SUCC $ SUCC $ ZERO) (EQ (SUCC $ SUCC $ SUCC $ ZERO) ZERO (APP (APP (_) ZERO) (SUCC ZERO))))
-- notation t " [ " σ " ]t " => SUBST_Tm σ t
