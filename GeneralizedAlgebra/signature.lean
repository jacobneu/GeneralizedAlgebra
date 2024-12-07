import Lean

open Lean Elab Meta


mutual
  inductive preCon : Type where
  | preEMPTY : preCon
  | preEXTEND : preCon → preTy → preCon

  -- inductive preSub : Type where
  -- | preEPSILON : preCon → preSub
  -- | preID : preCon → preSub
  -- | preCOMP : preSub → preSub → preSub
  -- | prePAIR : preSub → preTm → preSub
  -- | prePROJ1 : preSub → preSub

  inductive preTy : Type where
  | preUU : preTy
  | preEL : preTm → preTy
  | prePI : preTm → preTy → preTy

  inductive preTm : Type where
  | VAR : Nat → preTm
  | preAPP : preTm → preTm → preTm
end

open preCon preTy preTm Nat


def wkTm : preTm → preTm
| (VAR n) => VAR (succ n)
| (preAPP f x) => preAPP (wkTm f) (wkTm x)
def wkTy : preTy → preTy
| preUU => preUU
| (preEL X) => preEL (wkTm X)
| (prePI X Y) => prePI (wkTm X) (wkTy Y)
def sub1Tm (t : preTm) : preTm → preTm
| (VAR 0) => t
| (VAR (succ n)) => VAR n
| (preAPP f x) => preAPP (sub1Tm t f) (sub1Tm t x)
def sub1Ty (t : preTm) : preTy → preTy
| preUU => preUU
| (preEL X) => preEL (sub1Tm t X)
| (prePI X Y) => prePI (sub1Tm t X) (sub1Ty t Y)

  mutual
    inductive wfCon : preCon → Prop where
    | wfEMPTY : wfCon preEMPTY
    | wfEXTEND : {Γ : preCon} → {A : preTy} → wfCon Γ → wfTy Γ A → wfCon (preEXTEND Γ A)

    inductive wfTy : preCon → preTy → Prop where
    | wfUU : {Γ : preCon} → {_ : wfCon Γ} → wfTy Γ preUU
    | wfEL : {Γ : preCon} → {X : preTm} → {_ : wfCon Γ} → wfTm Γ preUU X → wfTy Γ (preEL X)
    | wfPI : {Γ : preCon} → {X : preTm} → {Y : preTy} → {_ : wfCon Γ} → wfTm Γ preUU X → wfTy (preEXTEND Γ (preEL X)) Y → wfTy Γ (prePI X Y)
    | wfwkTy : {Γ : preCon} → {A B : preTy} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfTy Γ B → wfTy (preEXTEND Γ A) (wkTy B)

    inductive wfTm : preCon → preTy → preTm → Prop where
    | wfVAR0 : {Γ : preCon} → {A : preTy} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfTm (preEXTEND Γ A) (wkTy A) (VAR 0)
    | wfVARsuc : {Γ : preCon} → {A B : preTy} → {_ : wfCon Γ} → {_ : wfTy Γ A} → {_ : wfTy Γ B} → {n : Nat} → wfTm Γ B (VAR n) → wfTm (preEXTEND Γ A) (wkTy B) (VAR (succ n))
    | wfAPP : {Γ : preCon} → {X : preTm} → {Y : preTy} → {f : preTm} → {x : preTm} → {_ : wfCon Γ} → {_ : wfTm Γ preUU X} → {_ : wfTy (preEXTEND Γ (preEL X)) Y} → wfTm Γ (prePI X Y) f → wfTm Γ (preEL X) x → wfTm Γ (sub1Ty x Y) (preAPP f x)
  end

open wfCon wfTy wfTm

def Con : Type := { Γ : preCon // wfCon Γ }
def Ty (Γ : Con) : Type := { A : preTy // wfTy Γ.1 A}
def Tm (Γ : Con) (A : Ty Γ) : Type := { t : preTm // wfTm Γ.1 A.1 t}

def EMPTY : Con := ⟨ preEMPTY , wfEMPTY ⟩
def EXTEND (Γ : Con) (A : Ty Γ) : Con :=
  ⟨ preEXTEND Γ.1 A.1 , wfEXTEND Γ.2 A.2 ⟩
def UU {Γ : Con} : Ty Γ := ⟨preUU , @wfUU _ Γ.2⟩
def EL {Γ : Con} (X : Tm Γ UU) : Ty Γ :=
⟨ preEL X.1, @wfEL _ _ Γ.2 X.2 ⟩
def WkTy {Γ : Con}{A : Ty Γ} (B : Ty Γ) : Ty (EXTEND Γ A) :=
⟨ wkTy B.1 , @wfwkTy _ _ _ Γ.2 A.2 B.2 ⟩
def PI {Γ : Con} (X : Tm Γ UU) (Y : Ty (EXTEND Γ (EL X))) : Ty Γ :=
⟨prePI X.1 Y.1, @wfPI _ _ _ Γ.2 X.2 Y.2⟩

-- inductive isWk : Con → preTy → Type where
-- | wkZero : {Γ : Con} → (A : Ty Γ) → isWk Γ A.1
-- | wkSucc : {Γ : Con} → {A : preTy} → isWk Γ A → (B : Ty Γ) → isWk (EXTEND Γ B) A
-- open isWk
-- inductive wkTypes : Con →  Nat → Type where
-- | wkZero : {Γ : Con} → Ty Γ → wkTypes Γ 0
-- | wkSucc : (Γ : Con) → {n : Nat} → (B : Ty Γ) → wkTypes Γ n → wkTypes (EXTEND Γ B) (succ n)
-- open wkTypes

-- def nWkTy {Γ : Con} : (n : Nat) → wkTypes Γ n → Ty Γ
-- | 0, wkZero A => A
-- | succ n, wkSucc Γ B A => WkTy (nWkTy n A)

-- def nWkTy  {Γ : Con}{A : preTy} : isWk Γ A → Ty Γ
-- | wkZero A => A
-- | wkSucc h B => WkTy (nWkTy h)

-- inductive Tel : Con → Type where
-- | telZero : {Γ : Con} → Ty Γ → Tel Γ
-- -- | telSucc : {Γ : Con}
-- open Tel

-- def extCon {Γ : Con} : Tel Γ → Con
-- | telZero A => EXTEND Γ A

-- def extTy {Γ : Con} : (T : Tel Γ) → Ty (extCon T)
-- | telZero A => WkTy A

def V0 {Γ : Con}{A : Ty Γ} : Tm (EXTEND Γ A) (WkTy A) :=
⟨ VAR 0 , @wfVAR0 _ _ Γ.2 A.2 ⟩
def V1 {Γ : Con}{A : Ty Γ}{B : Ty (EXTEND Γ A)} : Tm (EXTEND (EXTEND Γ A) B) (WkTy (WkTy A)) :=
⟨VAR 1,@wfVARsuc _ _ _ (EXTEND Γ A).2 B.2 (WkTy A).2 _ V0.2 ⟩
def V2 {Γ : Con}{A : Ty Γ}{B : Ty (EXTEND Γ A)}{C : Ty (EXTEND (EXTEND Γ A) B)} : Tm (EXTEND (EXTEND (EXTEND Γ A) B) C) (WkTy (WkTy (WkTy A))) :=
⟨VAR 2, @wfVARsuc _ _ _ (EXTEND (EXTEND Γ A) B).2 C.2 (WkTy (WkTy A)).2 _ V1.2⟩
def V3 {Γ : Con}{A : Ty Γ}{B : Ty (EXTEND Γ A)}{C : Ty (EXTEND (EXTEND Γ A) B)}{D : Ty (EXTEND (EXTEND (EXTEND Γ A) B) C)} : Tm (EXTEND (EXTEND (EXTEND (EXTEND Γ A) B) C) D) (WkTy (WkTy (WkTy (WkTy A)))) :=
⟨VAR 3, @wfVARsuc _ _ _ (EXTEND (EXTEND (EXTEND Γ A) B) C).2 D.2 (WkTy (WkTy (WkTy A))).2 _ V2.2⟩

-- def V {Γ : Con} : (T : Tel Γ) → Tm (extCon T) (extTy T)
-- | telZero A => ⟨ VAR 0 , @wfVAR0 _ _ Γ.2 A.2 ⟩

-- def Vsuc {Γ : Con}{B : Ty Γ}{n : Nat}{A : wkTypes Γ n} :  Tm (EXTEND Γ B) (nWkTy (succ n) (wkSucc B A)) :=
-- ⟨VAR (succ n), @wfVARsuc _ _ _ _ _ _ _ _⟩
-- | wkZero _, v => ⟨wkTm v.1,_⟩
-- | wkSucc h' B', v => ⟨wkTm v.1,_⟩

-- def wfWkTm {Γ : Con}{n : Nat}{B : Ty Γ}{A : wkTypes Γ n}{t : preTm} : wfTm Γ.1 (nWkTy n A).1 t → wfTm (EXTEND Γ B).1 (nWkTy (succ n) (wkSucc B A)).1 (wkTm t):= _
-- def varCon {Γ:Con} : (n : Nat) →(A : wkTypes Γ n) → Con
-- | 0, wkZero A => EXTEND Γ A
-- | succ n, wkSucc Γ B A => EXTEND Γ B

-- def varTy  {Γ:Con} : (n : Nat) →(A : wkTypes Γ n) → Ty (varCon n A)
-- | 0, wkZero A => WkTy A
-- | succ n, wkSucc Γ B A =>

-- def V_helper {Γ : Con} : (n : Nat) → (A : wkTypes Γ n) → wfTm (EXTEND Γ (nWkTy n A)).1 (nWkTy (succ n) (wkSucc _ (nWkTy n A) A)).1 (VAR n)
-- | 0,wkZero A => @wfVAR0 _ _ Γ.2 A.2
-- | succ n, wkSucc Γ B A => @wfVARsuc _ _ _ (EXTEND Γ B).2 (nWkTy _ _).2 (nWkTy _ _).2 _ _

-- def V {Γ : Con} : (n : Nat) → (A : wkTypes Γ n) →
--   Tm (varCon n A) (nWkTy (succ n) (wkSucc _ _ A)) := ⟨VAR n,V_helper n A⟩

-- #check EXTEND (EXTEND (EXTEND EMPTY UU) (EL V0)) (PI (V1) (WkTy (EL V1)))
-- mutual
--   inductive Subst : Con → Con → Type where
--   | ε : {Γ : Con} → Subst Γ EMPTY
--   | PAIR : {Δ Γ : Con} → {A : Ty Γ} → (σ : Subst Δ Γ) → Tm Δ _ → Subst Δ (EXTEND Γ A)

--   def Subst_Ty : {Δ Γ : Con} → Ty Γ → Subst Δ Γ → Ty Δ := sorry
-- end


  -- inductive conv : goodTm → goodTm → Prop where
  -- | β :

--   def good₀ID {Γ : good₀Con} : good₀Sub Γ Γ :=
--     ⟨ preID Γ.1 , @wfID _ Γ.2 ⟩
--   def good₀COMP {Θ Δ Γ : good₀Con} (γ : good₀Sub Δ Γ) (δ : good₀Sub Θ Δ) : good₀Sub Θ Γ :=
--     ⟨ preCOMP γ.1 δ.1 , @wfCOMP _ _ _ _ _ Θ.2 Δ.2 Γ.2 δ.2 γ.2  ⟩
--   def good₀EMPTY : good₀Con :=
--     ⟨ preEMPTY , wfEMPTY ⟩
--   def good₀EPSILON {Γ : good₀Con} : good₀Sub Γ good₀EMPTY :=
--     ⟨ preEPSILON Γ.1 , @wfEPSILON _ Γ.2 ⟩
--   def good₀SUBST_Ty {Δ Γ : good₀Con} (σ : good₀Sub Δ Γ) (A : good₀Ty Γ) : good₀Ty Δ :=
--     ⟨ preSUBST_Ty σ.1 A.1 , @wfSUBST_Ty _ Γ.1 _ _ Δ.2 Γ.2 σ.2 A.2⟩
--   def good₀SUBST_Tm {Δ Γ : good₀Con} {A : good₀Ty Γ} (σ : good₀Sub Δ Γ) (t : good₀Tm Γ A) : good₀Tm Δ (good₀SUBST_Ty σ A) :=
--     ⟨ preSUBST_Tm σ.1 t.1 , @wfSUBST_Tm _ Γ.1 _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2 ⟩

--   def good₀EXTEND (Γ : good₀Con) (A : good₀Ty Γ) : good₀Con :=
--     ⟨ preEXTEND Γ.1 A.1 , @wfEXTEND _ _ Γ.2 A.2 ⟩
--   def good₀PAIR {Δ Γ : good₀Con} {A : good₀Ty Γ} (σ : good₀Sub Δ Γ) (t : good₀Tm Δ (good₀SUBST_Ty σ A)) : good₀Sub Δ (good₀EXTEND Γ A) :=
--     ⟨ prePAIR σ.1 t.1 , @wfPAIR _ _ _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2⟩
--   def good₀PROJ1 {Δ Γ : good₀Con} {A : good₀Ty Γ} (τ : good₀Sub Δ (good₀EXTEND Γ A)) : good₀Sub Δ Γ :=
--     ⟨ prePROJ1 τ.1 , @wfPROJ1 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩
--   def goodPROJ2 {Δ Γ : good₀Con} {A : good₀Ty Γ} (τ : good₀Sub Δ (good₀EXTEND Γ A)) : good₀Tm Δ (good₀SUBST_Ty (good₀PROJ1 τ) A) :=
--     ⟨ prePROJ2 τ.1 , @wfPROJ2 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩

--   def good₀UU {Γ : good₀Con} : good₀Ty Γ :=
--     ⟨ preUU , @wfUU Γ.1 Γ.2 ⟩
--   def good₀EL {Γ : good₀Con} (X : good₀Tm Γ good₀UU) : good₀Ty Γ :=
--     ⟨ preEL X.1 , @wfEL _ _ Γ.2 X.2⟩
--   def good₀PI {Γ : good₀Con} (X : good₀Tm Γ good₀UU) (Y : good₀Ty (good₀EXTEND Γ (good₀EL X))) : good₀Ty Γ :=
--     ⟨ prePI X.1 Y.1 , @wfPI _ _ _ Γ.2 X.2 Y.2⟩
--   -- TODO: goodAPP
--   -- TODO: goodLAM
--   -- TODO: weakening (to state stablility of goodPI under substitution)

--   inductive conv₀Ty : {Γ : good₀Con} → good₀Ty Γ → good₀Ty Γ → Prop where
--   | SUBST_ID : (Γ : good₀Con) → (A : good₀Ty Γ) → conv₀Ty (good₀SUBST_Ty good₀ID A) A
--   | SUBST_COMP : {Θ Δ Γ : good₀Con} → {A : good₀Ty Γ} → (γ : good₀Sub Δ Γ) → (δ : good₀Sub Θ Δ) → conv₀Ty (good₀SUBST_Ty (good₀COMP γ δ) A) (good₀SUBST_Ty δ (good₀SUBST_Ty γ A))
--   | SUBST_UU : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → conv₀Ty (good₀SUBST_Ty σ good₀UU) good₀UU
--   -- | SUBST_EL : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → (X : good₀Tm Γ good₀UU) → conv₀Ty (good₀SUBST_Ty σ (good₀EL X)) (good₀EL (good₀SUBST_Tm σ X))
--   -- | SUBST_PI : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → {X : good₀Tm Γ good₀UU} → {Y : good₀Ty (good₀EXTEND Γ (good₀EL X))} → conv₀Ty (good₀SUBST_Ty σ (good₀PI X Y)) (good₀PI (good₀SUBST_Tm σ X) _)

--   inductive conv₀Sub : {Δ Γ : good₀Con} → good₀Sub Δ Γ → good₀Sub Δ Γ → Prop where
--   | ASS : {Ξ Θ Δ Γ : good₀Con} → (ϑ : good₀Sub Ξ Θ) → (δ : good₀Sub Θ Δ) → (γ : good₀Sub Δ Γ) → conv₀Sub (good₀COMP (good₀COMP γ δ) ϑ) (good₀COMP γ (good₀COMP δ ϑ))
--   | IDL : {Δ Γ : good₀Con} → (γ : good₀Sub Δ Γ) → conv₀Sub (good₀COMP good₀ID γ) γ
--   | IDR : {Δ Γ : good₀Con} → (γ : good₀Sub Δ Γ) → conv₀Sub (good₀COMP γ good₀ID) γ
--   | EPSILON_ETA : {Γ : good₀Con} → (σ : good₀Sub Γ good₀EMPTY) → conv₀Sub σ good₀EPSILON
--   | PAIR_BETA_1 : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → {A : good₀Ty Γ} → {t : good₀Tm Δ (good₀SUBST_Ty σ A)} → conv₀Sub (good₀PROJ1 (good₀PAIR σ t)) σ
--   -- | PAIR_ETA : {Δ Γ : good₀Con} → {A : good₀Ty Γ} → {τ : good₀Sub Δ (good₀EXTEND Γ A)} → conv₀Sub (good₀PAIR (good₀PROJ1 τ) (good₀PROJ2 τ)) τ
--   -- | PAIR_COMP : {Θ Δ Γ : good₀Con} → {δ : good₀Sub Θ Δ} → {σ : good₀Sub Δ Γ} → {A : good₀Ty Γ} → {t : good₀Tm Δ (good₀SUBST_Ty σ A)} → conv₀Sub (good₀COMP (good₀PAIR σ t) δ) (good₀PAIR (good₀COMP σ δ) (good₀SUBST_Tm δ t))

--   -- inductive convTm : {Γ : goodCon} → {A : goodTy Γ} → goodTm Γ A → goodTm Γ A → Prop
--   -- | EXTEND_BETA_2 : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → {A : goodTy Γ} → {t : goodTm Δ (goodSUBST_Ty σ A)} → convTm (goodPROJ2 (goodPAIR σ t)) t
--   -- | SUBST_APP :
--   -- | SUBST_LAM
--   -- | PI_BETA
--   -- | PI_ETA

-- #check Quot.lift

-- def good₁Con : Type := good₀Con
-- def good₁Sub (Γ Δ : good₁Con) : Type := Quot (@conv₀Sub Γ Δ)
-- def good₁Ty (Γ : good₁Con) : Type := Quot (@conv₀Ty Γ)

-- theorem lemm {Γ : good₁Con} (A B : good₀Ty Γ) : conv₀Ty A B → good₀Tm Γ A = good₀Tm Γ B := by
--   intro h
--   induction h with
--   | SUBST_ID X => rcases X with ⟨x,y⟩; cases x;
--   | SUBST_COMP => sorry
--   | SUBST_UU => sorry
--   -- induction



-- def good₁Tm (Γ : good₁Con) : good₁Ty Γ → Type := Quot.lift (good₀Tm Γ) lemm


-- -- def elabIMPLit : Syntax → MetaM
-- --   -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
-- --   -- `mkNatLit` creates an `Expr` from a `Nat`
-- --   | `(imp_lit| $n:num) => mkAppM ``IMPLit.nat  #[mkNatLit n.getNat]
-- --   | `(imp_lit| true  ) => mkAppM ``IMPLit.bool #[.const ``Bool.true []]
-- --   | `(imp_lit| false ) => mkAppM ``IMPLit.bool #[.const ``Bool.false []]
-- --   | _ => throwUnsupportedSyntax
