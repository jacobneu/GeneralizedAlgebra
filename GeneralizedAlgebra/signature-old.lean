import Lean

open Lean Elab Meta


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

def v0 : preTm := prePROJ2 (preID (preEXTEND preEMPTY preUU))
def preAPP' (Γ : preCon) (f : preTm) (x : preTm) : preTm :=
   preSUBST_Tm (prePAIR (preID Γ) x) (preAPP f)

def preCTXAPPEND (old : preCon) : preCon → preCon
| preEMPTY => old
| (preEXTEND Δ A) => preEXTEND (preCTXAPPEND old Δ) A

def GAT_sig : Type := preCon

set_option hygiene false





-- declare_syntax_cat gat_ty
-- syntax "U"       : gat_ty
-- syntax "(" gat_ty ")" : gat_ty


-- declare_syntax_cat gat_tm
-- syntax ident     : gat_tm
-- syntax "(" gat_tm ")" : gat_tm
-- syntax gat_tm gat_tm : gat_tm
-- syntax gat_tm : gat_ty

-- declare_syntax_cat gat_decl
-- syntax ident ":" gat_ty : gat_decl

-- declare_syntax_cat gat_arg
-- syntax "(" ident ":" gat_tm ")" : gat_arg
-- syntax "(" "_" ":" gat_tm ")" : gat_arg
-- syntax gat_tm : gat_arg

-- syntax gat_arg "⇒" gat_ty : gat_ty

-- declare_syntax_cat ident_list
-- syntax ident : ident_list
-- syntax "_" : ident_list
-- syntax ident_list "," "_" : ident_list
-- syntax ident_list "," ident : ident_list

-- declare_syntax_cat gat_con
-- syntax "⬝" : gat_con
-- syntax gat_decl : gat_con
-- syntax gat_con "," gat_decl : gat_con
-- syntax "include" ident "as" "(" ident_list ");" gat_con : gat_con

-- partial def elabGATTm (vars : String → MetaM Expr) : Syntax → MetaM Expr
-- | `(gat_tm| ( $g:gat_tm ) ) => elabGATTm vars g
-- -- | `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
-- --       let t1 ← elabGATTm vars g1
-- --       let t2 ← elabGATTm vars g2
-- --       mkAppM  ``preAPP #[t1]
-- | `(gat_tm| $i:ident ) => vars i.getId.toString
-- | _ => throwUnsupportedSyntax

-- partial def elabGATArg (vars : String → MetaM Expr) : Syntax → MetaM Expr
-- | `(gat_arg| ( $_:ident : $g:gat_tm ) ) => elabGATTm vars g
-- | `(gat_arg| ( _ : $g:gat_tm ) ) => elabGATTm vars g
-- | `(gat_arg| $g:gat_tm ) => elabGATTm vars g
-- | _ => throwUnsupportedSyntax


-- partial def elabGATTy (vars : String → MetaM Expr) : Syntax → MetaM Expr
-- | `(gat_ty| ( $g:gat_ty ) ) => elabGATTy vars g
-- | `(gat_ty| U ) => return .const ``preUU []
-- | `(gat_ty| $x:gat_tm ) => do
--   let t ← elabGATTm vars x
--   mkAppM ``preEL #[t]
-- | `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
--   let domain ← elabGATArg vars T
--   let codomain ← elabGATTy vars T'
--   mkAppM  ``prePI #[domain,codomain]
-- | _ => throwUnsupportedSyntax

-- partial def elab_ident_list (oldCtx newCtx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (Expr × (String → MetaM Expr))
-- | `(ident_list| $i:ident ) => do
--   let newVars := λ s =>
--     if s=i.getId.toString
--     then return (.const ``v0 [])
--     else vars s
--   let appendedCtx ← mkAppM ``preCTXAPPEND #[oldCtx,newCtx]
--   return (appendedCtx,newVars)
-- | `(ident_list| $is:ident_list , $i:ident ) => do
--   let (appendedCtx,othervars) ← elab_ident_list oldCtx newCtx vars is
--   let newVars := λ s =>
--     if s=i.getId.toString
--     then return (.const ``v0 [])
--     else do
--       let old ← othervars s
--       let ID ← mkAppM ``preID #[appendedCtx]
--       let p ← mkAppM ``prePROJ1 #[ID]
--       mkAppM ``preSUBST_Tm #[ p , old]
--   return (appendedCtx,newVars)
-- | _ => throwUnsupportedSyntax

-- -- Returns (identifier , type)
-- partial def elabGATdecl (vars : String → MetaM Expr) : Syntax → MetaM (String × Expr)
-- | `(gat_decl| $i:ident : $g:gat_ty ) => do
--     let T ← elabGATTy vars g
--     return (i.getId.toString,T)
-- | _ => throwUnsupportedSyntax

-- partial def elabGATCon_core (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (Expr × (String → MetaM Expr))
-- | `(gat_con| ⬝ ) => return (.const ``preEMPTY [] , λ _ => throwUnsupportedSyntax)
-- | `(gat_con| $rest:gat_con , $d:gat_decl ) => do
--   let (C , restVars) ← elabGATCon_core ctx vars rest
--   let (i,T) ← elabGATdecl restVars d
--   let res ← mkAppM ``preEXTEND #[C, T]
--   let newVars := λ s =>
--     if s=i
--     then return (.const ``v0 [])
--     else do
--       let old ← restVars s
--       let ID ← mkAppM ``preID #[res]
--       let p ← mkAppM ``prePROJ1 #[ID]
--       mkAppM ``preSUBST_Tm #[ p , old]
--   return (res, newVars)
-- | `(gat_con| $d:gat_decl ) => do
--   let (i,T) ← elabGATdecl vars d
--   let newVars := λ s =>
--     if s=i
--     then return (.const ``v0 [])
--     else do
--       let old ← vars s
--       let ID ← mkAppM ``preID #[ctx]
--       let p ← mkAppM ``prePROJ1 #[ID]
--       mkAppM ``preSUBST_Tm #[ p , old]
--   let res ← mkAppM ``preEXTEND #[ctx, T]
--   return (res, newVars)
-- | `(gat_con| include $g:ident as ( $is:ident_list ); $rest:gat_con ) => do
--   let (newCon,newVars) ← elab_ident_list ctx (.const g.getId []) vars is
--   elabGATCon_core newCon newVars rest
-- | _ => throwUnsupportedSyntax

-- partial def elabGATCon (s : Syntax) : MetaM Expr := do
--   let (res,_) ← elabGATCon_core (.const ``preEMPTY []) (λ _ => throwUnsupportedSyntax) s
--   return res

-- elab g:gat_con : term => elabGATCon g



-- @[app_unexpander preTy.preUU]
-- def unexpandUU : Lean.PrettyPrinter.Unexpander
--   | `($(_)) => `(UU)
-- @[app_unexpander preTy.prePI]
-- def unexpandPI : Lean.PrettyPrinter.Unexpander
--   | `($(_) $dom $cod) => `($dom -> $cod)
--   | _ => throw ()
-- @[app_unexpander preCon.preEMPTY]
-- def unexpandEMPTY : Lean.PrettyPrinter.Unexpander
--   | `($(_)) => `(⬝)
--   -- | _ => throw ()
-- @[app_unexpander preCon.preEXTEND]
-- def unexpandEXTEND : Lean.PrettyPrinter.Unexpander
--   | `($(_) $C $T) =>
--     match C with
--     | `(⬝) => `($T)
--     | _ => `($C ▸ $T)
--   | _ => throw ()
-- @[app_unexpander preTy.preEL]
-- def unexpandEL : Lean.PrettyPrinter.Unexpander
--   | `($(_) $code) => `(El $code)
--   | _ => throw ()
-- @[app_unexpander preSub.prePROJ1]
-- def unexpandPROJ1 : Lean.PrettyPrinter.Unexpander
--   | `($(_) $code) =>
--     match code with
--     | `(preID $_) => `(wk)
--     | _ => `(π₁ $code)
--   | _ => throw ()
-- @[app_unexpander preTm.preSUBST_Tm]
-- def unexpandSUBST_Tm : Lean.PrettyPrinter.Unexpander
--   | `($(_) $sigma $t) =>
--     match sigma with
--     | `(wk) => match t with
--       | `($n:num) => match n.getNat with
--         | 0 => `(1) | 1 => `(2) | 2 => `(3) | 3 => `(4) | 4 => `(5) | 5 => `(6) | 6 => `(7) | 7 => `(8) | 8 => `(9) | 9 => `(10) | 10 => `(11)
--         | _ => throw ()
--       | _ => `($t[wk])
--     | _ => `($t[$sigma])
--   | _ => throw ()
-- @[app_unexpander preTm.prePROJ2]
-- def unexpandPROJ2 : Lean.PrettyPrinter.Unexpander
--   | `($(_) $code) =>
--     match code with
--     | `(preID $_) => `(0)
--     | _ => `(π₂ $code)
--   | _ => throw ()


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

  def good₀Con : Type := { Γ : preCon // wfCon Γ }
  def good₀Sub (Δ Γ : good₀Con) : Type := { σ : preSub // wfSub Δ.1 Γ.1 σ }
  def good₀Ty (Γ : good₀Con) : Type := { A : preTy // wfTy Γ.1 A}
  def good₀Tm (Γ : good₀Con) (A : good₀Ty Γ) : Type := { t : preTm // wfTm Γ.1 A.1 t}

  def good₀ID {Γ : good₀Con} : good₀Sub Γ Γ :=
    ⟨ preID Γ.1 , @wfID _ Γ.2 ⟩
  def good₀COMP {Θ Δ Γ : good₀Con} (γ : good₀Sub Δ Γ) (δ : good₀Sub Θ Δ) : good₀Sub Θ Γ :=
    ⟨ preCOMP γ.1 δ.1 , @wfCOMP _ _ _ _ _ Θ.2 Δ.2 Γ.2 δ.2 γ.2  ⟩
  def good₀EMPTY : good₀Con :=
    ⟨ preEMPTY , wfEMPTY ⟩
  def good₀EPSILON {Γ : good₀Con} : good₀Sub Γ good₀EMPTY :=
    ⟨ preEPSILON Γ.1 , @wfEPSILON _ Γ.2 ⟩
  def good₀SUBST_Ty {Δ Γ : good₀Con} (σ : good₀Sub Δ Γ) (A : good₀Ty Γ) : good₀Ty Δ :=
    ⟨ preSUBST_Ty σ.1 A.1 , @wfSUBST_Ty _ Γ.1 _ _ Δ.2 Γ.2 σ.2 A.2⟩
  def good₀SUBST_Tm {Δ Γ : good₀Con} {A : good₀Ty Γ} (σ : good₀Sub Δ Γ) (t : good₀Tm Γ A) : good₀Tm Δ (good₀SUBST_Ty σ A) :=
    ⟨ preSUBST_Tm σ.1 t.1 , @wfSUBST_Tm _ Γ.1 _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2 ⟩

  def good₀EXTEND (Γ : good₀Con) (A : good₀Ty Γ) : good₀Con :=
    ⟨ preEXTEND Γ.1 A.1 , @wfEXTEND _ _ Γ.2 A.2 ⟩
  def good₀PAIR {Δ Γ : good₀Con} {A : good₀Ty Γ} (σ : good₀Sub Δ Γ) (t : good₀Tm Δ (good₀SUBST_Ty σ A)) : good₀Sub Δ (good₀EXTEND Γ A) :=
    ⟨ prePAIR σ.1 t.1 , @wfPAIR _ _ _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2⟩
  def good₀PROJ1 {Δ Γ : good₀Con} {A : good₀Ty Γ} (τ : good₀Sub Δ (good₀EXTEND Γ A)) : good₀Sub Δ Γ :=
    ⟨ prePROJ1 τ.1 , @wfPROJ1 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩
  def goodPROJ2 {Δ Γ : good₀Con} {A : good₀Ty Γ} (τ : good₀Sub Δ (good₀EXTEND Γ A)) : good₀Tm Δ (good₀SUBST_Ty (good₀PROJ1 τ) A) :=
    ⟨ prePROJ2 τ.1 , @wfPROJ2 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩

  def good₀UU {Γ : good₀Con} : good₀Ty Γ :=
    ⟨ preUU , @wfUU Γ.1 Γ.2 ⟩
  def good₀EL {Γ : good₀Con} (X : good₀Tm Γ good₀UU) : good₀Ty Γ :=
    ⟨ preEL X.1 , @wfEL _ _ Γ.2 X.2⟩
  def good₀PI {Γ : good₀Con} (X : good₀Tm Γ good₀UU) (Y : good₀Ty (good₀EXTEND Γ (good₀EL X))) : good₀Ty Γ :=
    ⟨ prePI X.1 Y.1 , @wfPI _ _ _ Γ.2 X.2 Y.2⟩
  -- TODO: goodAPP
  -- TODO: goodLAM
  -- TODO: weakening (to state stablility of goodPI under substitution)

  inductive conv₀Ty : {Γ : good₀Con} → good₀Ty Γ → good₀Ty Γ → Prop where
  | SUBST_ID : (Γ : good₀Con) → (A : good₀Ty Γ) → conv₀Ty (good₀SUBST_Ty good₀ID A) A
  | SUBST_COMP : {Θ Δ Γ : good₀Con} → {A : good₀Ty Γ} → (γ : good₀Sub Δ Γ) → (δ : good₀Sub Θ Δ) → conv₀Ty (good₀SUBST_Ty (good₀COMP γ δ) A) (good₀SUBST_Ty δ (good₀SUBST_Ty γ A))
  | SUBST_UU : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → conv₀Ty (good₀SUBST_Ty σ good₀UU) good₀UU
  -- | SUBST_EL : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → (X : good₀Tm Γ good₀UU) → conv₀Ty (good₀SUBST_Ty σ (good₀EL X)) (good₀EL (good₀SUBST_Tm σ X))
  -- | SUBST_PI : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → {X : good₀Tm Γ good₀UU} → {Y : good₀Ty (good₀EXTEND Γ (good₀EL X))} → conv₀Ty (good₀SUBST_Ty σ (good₀PI X Y)) (good₀PI (good₀SUBST_Tm σ X) _)

  inductive conv₀Sub : {Δ Γ : good₀Con} → good₀Sub Δ Γ → good₀Sub Δ Γ → Prop where
  | ASS : {Ξ Θ Δ Γ : good₀Con} → (ϑ : good₀Sub Ξ Θ) → (δ : good₀Sub Θ Δ) → (γ : good₀Sub Δ Γ) → conv₀Sub (good₀COMP (good₀COMP γ δ) ϑ) (good₀COMP γ (good₀COMP δ ϑ))
  | IDL : {Δ Γ : good₀Con} → (γ : good₀Sub Δ Γ) → conv₀Sub (good₀COMP good₀ID γ) γ
  | IDR : {Δ Γ : good₀Con} → (γ : good₀Sub Δ Γ) → conv₀Sub (good₀COMP γ good₀ID) γ
  | EPSILON_ETA : {Γ : good₀Con} → (σ : good₀Sub Γ good₀EMPTY) → conv₀Sub σ good₀EPSILON
  | PAIR_BETA_1 : {Δ Γ : good₀Con} → {σ : good₀Sub Δ Γ} → {A : good₀Ty Γ} → {t : good₀Tm Δ (good₀SUBST_Ty σ A)} → conv₀Sub (good₀PROJ1 (good₀PAIR σ t)) σ
  -- | PAIR_ETA : {Δ Γ : good₀Con} → {A : good₀Ty Γ} → {τ : good₀Sub Δ (good₀EXTEND Γ A)} → conv₀Sub (good₀PAIR (good₀PROJ1 τ) (good₀PROJ2 τ)) τ
  -- | PAIR_COMP : {Θ Δ Γ : good₀Con} → {δ : good₀Sub Θ Δ} → {σ : good₀Sub Δ Γ} → {A : good₀Ty Γ} → {t : good₀Tm Δ (good₀SUBST_Ty σ A)} → conv₀Sub (good₀COMP (good₀PAIR σ t) δ) (good₀PAIR (good₀COMP σ δ) (good₀SUBST_Tm δ t))

  -- inductive convTm : {Γ : goodCon} → {A : goodTy Γ} → goodTm Γ A → goodTm Γ A → Prop
  -- | EXTEND_BETA_2 : {Δ Γ : goodCon} → {σ : goodSub Δ Γ} → {A : goodTy Γ} → {t : goodTm Δ (goodSUBST_Ty σ A)} → convTm (goodPROJ2 (goodPAIR σ t)) t
  -- | SUBST_APP :
  -- | SUBST_LAM
  -- | PI_BETA
  -- | PI_ETA

#check Quot.lift

def good₁Con : Type := good₀Con
def good₁Sub (Γ Δ : good₁Con) : Type := Quot (@conv₀Sub Γ Δ)
def good₁Ty (Γ : good₁Con) : Type := Quot (@conv₀Ty Γ)

theorem lemm {Γ : good₁Con} (A B : good₀Ty Γ) : conv₀Ty A B → good₀Tm Γ A = good₀Tm Γ B := by
  intro h
  induction h with
  | SUBST_ID X => rcases X with ⟨x,y⟩; cases x;
  | SUBST_COMP => sorry
  | SUBST_UU => sorry
  -- induction



def good₁Tm (Γ : good₁Con) : good₁Ty Γ → Type := Quot.lift (good₀Tm Γ) lemm


-- def elabIMPLit : Syntax → MetaM
--   -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
--   -- `mkNatLit` creates an `Expr` from a `Nat`
--   | `(imp_lit| $n:num) => mkAppM ``IMPLit.nat  #[mkNatLit n.getNat]
--   | `(imp_lit| true  ) => mkAppM ``IMPLit.bool #[.const ``Bool.true []]
--   | `(imp_lit| false ) => mkAppM ``IMPLit.bool #[.const ``Bool.false []]
--   | _ => throwUnsupportedSyntax
