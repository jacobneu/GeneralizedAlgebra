mutual
  inductive preCon : Type where
  | preEMPTY : preCon
  | preEXTEND : preCon → preTy → preCon

  inductive preSub : Type where
  | preEPSILON : preCon → preSub
  | preID : preCon → preSub
  | preCOMP : preSub → preSub → preSub
  | prePAIR : preSub → preTm → preSub
  | prePROJ1 : preSub → preSub

  inductive preTy : Type where
  | preSUBST_Ty : preSub → preTy → preTy
  | preUU : preTy
  | preEL : preTm → preTy
  | prePI : preTm → preTy → preTy

  inductive preTm : Type where
  | preSUBST_Tm : preSub → preTm → preTm
  | prePROJ2 : preSub → preTm
  | preAPP : preTm → preTm
  | preLAM : preTm → preTm
end

open preCon preSub preTy preTm

mutual
  inductive wfCon : preCon → Prop where
  | wfEMPTY : wfCon preEMPTY
  | wfEXTEND : {Γ : preCon} → {A : preTy} → wfCon Γ → wfTy Γ A → wfCon (preEXTEND Γ A)

  inductive wfSub : preCon → preCon → preSub → Prop
  | wfEPSILON : {Γ : preCon} → {_ : wfCon Γ} → wfSub Γ preEMPTY (preEPSILON Γ)
  | wfID : {Γ : preCon} → {_ : wfCon Γ} → wfSub Γ Γ (preID Γ)
  | wfCOMP : {Θ Δ Γ : preCon} → {δ γ : preSub} → {_ :wfCon Θ} → {_ :wfCon Δ} → {_ : wfCon Γ} → wfSub Θ Δ δ → wfSub Δ Γ γ → wfSub Θ Γ (preCOMP γ δ)
  | wfPAIR : {Δ Γ : preCon} → {A : preTy} → {σ : preSub} → {t : preTm} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ Γ σ → wfTm Δ (preSUBST_Ty σ A) t → wfSub Δ (preEXTEND Γ A) (prePAIR σ t)
  | wfPROJ1 : {Δ Γ : preCon} → {A : preTy} → {τ : preSub} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ (preEXTEND Γ A) τ → wfSub Δ Γ (prePROJ1 τ)

  inductive wfTy : preCon → preTy → Prop where
  | wfSUBST_Ty : {Δ Γ : preCon} → {σ : preSub} → {A : preTy} → {_ : wfCon Δ} → {_ : wfCon Γ} → wfSub Δ Γ σ→ wfTy Γ A → wfTy Δ (preSUBST_Ty σ A)
  | wfUU : {Γ : preCon} → {_ : wfCon Γ} → wfTy Γ preUU
  | wfEL : {Γ : preCon} → {X : preTm} → {_ : wfCon Γ} → wfTm Γ preUU X → wfTy Γ (preEL X)
  | wfPI : {Γ : preCon} → {X : preTm} → {Y : preTy} → {_ : wfCon Γ} → wfTm Γ preUU X → wfTy (preEXTEND Γ (preEL X)) Y → wfTy Γ (prePI X Y)

  inductive wfTm : preCon → preTy → preTm → Prop where
  | wfSUBST_Tm : {Δ Γ : preCon} → {A : preTy} → {t : preTm} → {σ : preSub} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ Γ σ → wfTm Γ A t → wfTm Δ (preSUBST_Ty σ A) (preSUBST_Tm σ t)
  | wfPROJ2 : {Δ Γ : preCon} → {A : preTy} → {τ : preSub} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ (preEXTEND Γ A) τ → wfTm Δ (preSUBST_Ty (prePROJ1 τ) A) (prePROJ2 τ)
  | wfAPP : {Γ : preCon} → {X : preTm} → {Y : preTy} → {f : preTm} → {_ : wfCon Γ} → {_ : wfTm Γ preUU X} → {_ : wfTy (preEXTEND Γ (preEL X)) Y} → wfTm Γ (prePI X Y) f → wfTm (preEXTEND Γ (preEL X)) Y (preAPP f)
  | wfLAM : {Γ : preCon} → {X : preTm} → {Y : preTy} → {e : preTm} → {_ : wfCon Γ} → {_ : wfTm Γ preUU X} → {_ : wfTy (preEXTEND Γ (preEL X)) Y} → wfTm (preEXTEND Γ (preEL X)) Y e → wfTm Γ (preEL X) (preLAM e)
end

open wfCon wfSub wfTy wfTm

def goodCon : Type := { Γ : preCon // wfCon Γ }
def goodSub (Δ Γ : goodCon) : Type := { σ : preSub // wfSub Δ.1 Γ.1 σ }
def goodTy (Γ : goodCon) : Type := { A : preTy // wfTy Γ.1 A}
def goodTm (Γ : goodCon) (A : goodTy Γ) : Type := { t : preTm // wfTm Γ.1 A.1 t}

def goodID {Γ : goodCon} : goodSub Γ Γ :=
  ⟨ preID Γ.1 , @wfID _ Γ.2 ⟩
def goodCOMP {Θ Δ Γ : goodCon} (γ : goodSub Δ Γ) (δ : goodSub Θ Δ) : goodSub Θ Γ :=
  ⟨ preCOMP γ.1 δ.1 , @wfCOMP _ _ _ _ _ Θ.2 Δ.2 Γ.2 δ.2 γ.2  ⟩
def goodEMPTY : goodCon :=
  ⟨ preEMPTY , wfEMPTY ⟩
def goodEPSILON {Γ : goodCon} : goodSub Γ goodEMPTY :=
  ⟨ preEPSILON Γ.1 , @wfEPSILON _ Γ.2 ⟩
def goodSUBST_Ty {Δ Γ : goodCon} (σ : goodSub Δ Γ) (A : goodTy Γ) : goodTy Δ :=
  ⟨ preSUBST_Ty σ.1 A.1 , @wfSUBST_Ty _ Γ.1 _ _ Δ.2 Γ.2 σ.2 A.2⟩
def goodSUBST_Tm {Δ Γ : goodCon} {A : goodTy Γ} (σ : goodSub Δ Γ) (t : goodTm Γ A) : goodTm Δ (goodSUBST_Ty σ A) :=
  ⟨ preSUBST_Tm σ.1 t.1 , @wfSUBST_Tm _ Γ.1 _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2 ⟩

def goodEXTEND (Γ : goodCon) (A : goodTy Γ) : goodCon :=
  ⟨ preEXTEND Γ.1 A.1 , @wfEXTEND _ _ Γ.2 A.2 ⟩
def goodPAIR {Δ Γ : goodCon} {A : goodTy Γ} (σ : goodSub Δ Γ) (t : goodTm Δ (goodSUBST_Ty σ A)) : goodSub Δ (goodEXTEND Γ A) :=
  ⟨ prePAIR σ.1 t.1 , @wfPAIR _ _ _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2⟩
def goodPROJ1 {Δ Γ : goodCon} {A : goodTy Γ} (τ : goodSub Δ (goodEXTEND Γ A)) : goodSub Δ Γ :=
  ⟨ prePROJ1 τ.1 , @wfPROJ1 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩
def goodPROJ2 {Δ Γ : goodCon} {A : goodTy Γ} (τ : goodSub Δ (goodEXTEND Γ A)) : goodTm Δ (goodSUBST_Ty (goodPROJ1 τ) A) :=
  ⟨ prePROJ2 τ.1 , @wfPROJ2 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩

def goodUU {Γ : goodCon} : goodTy Γ :=
  ⟨ preUU , @wfUU Γ.1 Γ.2 ⟩
def goodEL {Γ : goodCon} (X : goodTm Γ goodUU) : goodTy Γ :=
  ⟨ preEL X.1 , @wfEL _ _ Γ.2 X.2⟩
def goodPI {Γ : goodCon} (X : goodTm Γ goodUU) (Y : goodTy (goodEXTEND Γ (goodEL X))) : goodTy Γ :=
  ⟨ prePI X.1 Y.1 , @wfPI _ _ _ Γ.2 X.2 Y.2⟩
-- TODO: goodAPP
-- TODO: goodLAM
-- TODO: weakening (to state stablility of goodPI under substitution)

inductive convTy : {Γ : goodCon} → goodTy Γ → goodTy Γ → Prop where
| SUBST_ID : {Γ : goodCon} → {A : goodTy Γ} → convTy (goodSUBST_Ty goodID A) A
| SUBST_COMP : {Θ Δ Γ : goodCon} → {A : goodTy Γ} → (γ : goodSub Δ Γ) → (δ : goodSub Θ Δ) → convTy (goodSUBST_Ty (goodCOMP γ δ) A) (goodSUBST_Ty δ (goodSUBST_Ty γ A))
| SUBST_UU : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → convTy (goodSUBST_Ty σ goodUU) goodUU
-- | SUBST_EL : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → (X : goodTm Γ goodUU) → convTy (goodSUBST_Ty σ (goodEL X)) (goodEL (goodSUBST_Tm σ X))
-- | SUBST_PI : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → {X : goodTm Γ goodUU} → {Y : goodTy (goodEXTEND Γ (goodEL X))} → convTy (goodSUBST_Ty σ (goodPI X Y)) (goodPI (goodSUBST_Tm σ X) _)

inductive convSub : {Δ Γ : goodCon} → goodSub Δ Γ → goodSub Δ Γ → Prop where
| ASS : {Ξ Θ Δ Γ : goodCon} → (ϑ : goodSub Ξ Θ) → (δ : goodSub Θ Δ) → (γ : goodSub Δ Γ) → convSub (goodCOMP (goodCOMP γ δ) ϑ) (goodCOMP γ (goodCOMP δ ϑ))
| IDL : {Δ Γ : goodCon} → (γ : goodSub Δ Γ) → convSub (goodCOMP goodID γ) γ
| IDR : {Δ Γ : goodCon} → (γ : goodSub Δ Γ) → convSub (goodCOMP γ goodID) γ
| EPSILON_ETA : {Γ : goodCon} → (σ : goodSub Γ goodEMPTY) → convSub σ goodEPSILON
| PAIR_BETA_1 : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → {A : goodTy Γ} → {t : goodTm Δ (goodSUBST_Ty σ A)} → convSub (goodPROJ1 (goodPAIR σ t)) σ
| PAIR_ETA : {Δ Γ : goodCon} → {A : goodTy Γ} → {τ : goodSub Δ (goodEXTEND Γ A)} → convSub (goodPAIR (goodPROJ1 τ) (goodPROJ2 τ)) τ
-- | PAIR_COMP : {Θ Δ Γ : goodCon} → {δ : goodSub Θ Δ} → {σ : goodSub Δ Γ} → {A : goodTy Γ} → {t : goodTm Δ (goodSUBST_Ty σ A)} → convSub (goodCOMP (goodPAIR σ t) δ) (goodPAIR (goodCOMP σ δ) (goodSUBST_Tm δ t))

inductive convTm : {Γ : goodCon} → {A : goodTy Γ} → goodTm Γ A → goodTm Γ A → Prop
-- | EXTEND_BETA_2 : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → {A : goodTy Γ} → {t : goodTm Δ (goodSUBST_Ty σ A)} → convTm (goodPROJ2 (goodPAIR σ t)) t
-- | SUBST_APP :
-- | SUBST_LAM
-- | PI_BETA
-- | PI_ETA
