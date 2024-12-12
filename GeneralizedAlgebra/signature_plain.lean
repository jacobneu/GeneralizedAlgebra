import Lean

open Lean Elab Meta

open Nat

mutual
  inductive Con : Type where
  | EMPTY : Con
  | EXTEND : Con → Ty → Con

  inductive Subst : Type where
  | EPSILON : Con → Subst
  | ID : Con → Subst
  | COMP : Subst → Subst → Subst
  | PAIR : Subst → Tm → Subst
  | PROJ1 : Subst → Subst

  inductive Ty : Type where
  | SUBST_Ty : Subst → Ty → Ty
  | UU : Ty
  | EL : Tm → Ty
  | PI : Tm → Ty → Ty
  | EQ : Tm → Tm → Ty

  inductive Tm : Type where
  | SUBST_Tm : Subst → Tm → Tm
  | PROJ2 : Subst → Tm
  | APP : Tm → Tm
end

open Con Subst Ty Tm


infixl:10 " ▷ " => EXTEND
notation t " [ " σ " ]t " => SUBST_Tm σ t

def wk (Γ : Con) (A : Ty) : Subst := PROJ1 (@ID (Γ ▷ A))
def V0 (Γ : Con) (T0 : Ty) : Tm := PROJ2 (@ID (Γ ▷ T0))
def V1 (Γ)(T1)(T0) := (@V0 Γ T0) [@wk (Γ ▷ T1) T0]t
def V2 (Γ)(T2)(T1)(T0) := (@V1 Γ T0 T1) [@wk (Γ ▷ T2 ▷ T1) T0]t
def V3 (Γ)(T3)(T2)(T1)(T0) := (@V2 Γ T0 T1 T2) [@wk (Γ ▷ T3 ▷ T2 ▷ T1) T0]t
def V4 (Γ)(T4)(T3)(T2)(T1)(T0) := (@V3 Γ T0 T1 T2 T3) [@wk (Γ ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V5 (Γ)(T5)(T4)(T3)(T2)(T1)(T0) := (@V4 Γ T0 T1 T2 T3 T4) [@wk (Γ ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V6 (Γ)(T6)(T5)(T4)(T3)(T2)(T1)(T0) := (@V5 Γ T0 T1 T2 T3 T4 T5) [@wk (Γ ▷ T6 ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V7 (Γ)(T7)(T6)(T5)(T4)(T3)(T2)(T1)(T0) := (@V6 Γ T0 T1 T2 T3 T4 T5 T6) [@wk (Γ ▷ T7 ▷ T6 ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V8 (Γ)(T8)(T7)(T6)(T5)(T4)(T3)(T2)(T1)(T0) := (@V7 Γ T0 T1 T2 T3 T4 T5 T6 T7) [@wk (Γ ▷ T8 ▷ T7 ▷ T6 ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V9 (Γ)(T9)(T8)(T7)(T6)(T5)(T4)(T3)(T2)(T1)(T0) := (@V8 Γ T0 T1 T2 T3 T4 T5 T6 T7 T8) [@wk (Γ ▷ T9 ▷ T8 ▷ T7 ▷ T6 ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V10 (Γ)(T10)(T9)(T8)(T7)(T6)(T5)(T4)(T3)(T2)(T1)(T0) := (@V9 Γ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) [@wk (Γ ▷ T10 ▷ T9 ▷ T8 ▷ T7 ▷ T6 ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t
def V11 (Γ)(T11)(T10)(T9)(T8)(T7)(T6)(T5)(T4)(T3)(T2)(T1)(T0) := (@V10 Γ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) [@wk (Γ ▷ T11 ▷ T10 ▷ T9 ▷ T8 ▷ T7 ▷ T6 ▷ T5 ▷ T4 ▷ T3 ▷ T2 ▷ T1) T0]t

def GAT : Type := Con

def deBruijn : Tm → Option Nat
| PROJ2 (ID _) => some 0
| t [ PROJ1 (ID _) ]t => do let res ← deBruijn t; return (succ res)
| _ => none

def paren (s:String):String :=
  if String.isNat s then s else "("++s++")"

mutual
  def Con_toString : Con → String
  | EMPTY => "⋄"
  | Γ ▷ A => (Con_toString Γ) ++ " ▷ " ++ (Ty_toString A)
  def Ty_toString : Ty → String
  | UU => "U"
  | EL X => "El " ++ paren (Tm_toString X)
  | PI X UU => "Π " ++ paren (Tm_toString X) ++ " U"
  | PI X Y => "Π " ++ paren (Tm_toString X) ++ " " ++ paren (Ty_toString Y)
  | EQ t t' => "Eq " ++ paren (Tm_toString t) ++ " " ++ paren (Tm_toString t')
  | SUBST_Ty σ T => (Ty_toString T) ++ " [ " ++ (Subst_toString σ) ++ " ]T"

  def Tm_toString (theTerm : Tm) : String :=
  match deBruijn theTerm with
  | some n => Nat.repr n
  | _ => match theTerm with
    | (APP f) [ PAIR (ID _) t ]t => (Tm_toString f) ++ " @ " ++ paren (Tm_toString t)
    | PROJ2 σ => "π₂ " ++ (Subst_toString σ)
    | APP f => "App " ++ paren (Tm_toString f)
    | t [ σ ]t => paren (Tm_toString t) ++ " [ " ++ (Subst_toString σ) ++ " ]t "
  def Subst_toString : Subst → String
  | PROJ1 (ID _) => "wk"
  | PROJ1 σ => "π₁ " ++ (Subst_toString σ)
  | PAIR σ t => (Subst_toString σ) ++ " , " ++ paren (Tm_toString t)
  | EPSILON _ => "ε"
  | COMP σ τ => (Subst_toString σ) ++ " ∘ " ++ (Subst_toString τ)
  | (ID _) => "id"
end


declare_syntax_cat gat_ty
syntax "U"       : gat_ty
syntax "(" gat_ty ")" : gat_ty


declare_syntax_cat gat_tm
syntax ident     : gat_tm
syntax "(" gat_tm ")" : gat_tm
syntax:60 gat_tm:60 gat_tm:61 : gat_tm
syntax gat_tm : gat_ty
syntax gat_tm " ≡ " gat_tm : gat_ty

declare_syntax_cat gat_decl
syntax ident ":" gat_ty : gat_decl

declare_syntax_cat gat_arg
syntax "(" ident ":" gat_tm ")" : gat_arg
syntax "(" "_" ":" gat_tm ")" : gat_arg
syntax gat_tm : gat_arg

syntax gat_arg "⇒" gat_ty : gat_ty

declare_syntax_cat ident_list
syntax ident : ident_list
syntax "_" : ident_list
syntax ident_list "," "_" : ident_list
syntax ident_list "," ident : ident_list

declare_syntax_cat con_inner
syntax gat_decl : con_inner
syntax con_inner "," gat_decl : con_inner
syntax "include" ident "as" "(" ident_list ");" con_inner : con_inner
declare_syntax_cat con_outer
syntax "⦃" "⦄" : con_outer
syntax "⦃" con_inner "⦄" : con_outer

declare_syntax_cat nouGAT_instr
syntax "[nouGAT|" "]" : nouGAT_instr
syntax "[nouGAT|" con_inner "]" : nouGAT_instr


partial def elabGATTm (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM Expr
| `(gat_tm| ( $g:gat_tm ) ) => elabGATTm ctx vars g
| `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
      let t1 ← elabGATTm ctx vars g1
      let Appt1 ← mkAppM ``APP #[t1]
      let t2 ← elabGATTm ctx vars g2
      let ID ← mkAppM ``ID #[ctx]
      let substt2 ← mkAppM ``PAIR #[ID,t2]
      mkAppM ``SUBST_Tm #[substt2,Appt1]
| `(gat_tm| $i:ident ) => vars i.getId.toString
| _ => throwUnsupportedSyntax


partial def elabGATArg (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (String × Expr)
| `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
  let t ← elabGATTm ctx vars g
  return (i.getId.toString,t)
| `(gat_arg| ( _ : $g:gat_tm ) ) => do
  let t ← elabGATTm ctx vars g
  return ("",t)
| `(gat_arg| $g:gat_tm ) => do
  let t ← elabGATTm ctx vars g
  return ("",t)
| _ => throwUnsupportedSyntax

partial def elabGATTy (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM Expr
| `(gat_ty| ( $g:gat_ty ) ) => elabGATTy ctx vars g
| `(gat_ty| U ) => return .const ``UU []
| `(gat_ty| $x:gat_tm ) => do
  let t ← elabGATTm ctx vars x
  mkAppM ``EL #[t]
| `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
  let (i,domain) ← elabGATArg ctx vars T
  let elDomain ← mkAppM ``EL #[domain]
  let newCtx ← mkAppM ``EXTEND #[ctx,elDomain]
  let newVars := λ s =>
    if s=i
    then mkAppM ``V0 #[ ctx , elDomain ]
    else do
      let old ← vars s
      let ID ← mkAppM ``ID #[newCtx]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old]
  let codomain ← elabGATTy newCtx newVars T'
  mkAppM  ``PI #[domain,codomain]
| `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
  let tt1 ← elabGATTm ctx vars t1
  let tt2 ← elabGATTm ctx vars t2
  mkAppM ``EQ #[tt1,tt2]
| _ => throwUnsupportedSyntax

partial def elabGATdecl (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (String × Expr)
| `(gat_decl| $i:ident : $g:gat_ty ) => do
    let T ← elabGATTy ctx vars g
    return (i.getId.toString,T)
| _ => throwUnsupportedSyntax



-- partial def elab_ident_list (oldCtx newCtx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (Expr × Expr × (String → MetaM Expr))
-- | `(ident_list| $i:ident ) => do
--   let T ← last_type
--   let newVars := λ s =>
--     if s=i.getId.toString
--     then mkAppM ``V0 #[ oldCtx , T ]
--     else vars s
--   let appendedCtx ← mkAppM ``preCTXAPPEND #[oldCtx,newCtx]
--   return (appendedCtx,newVars)
-- | `(ident_list| $is:ident_list , $i:ident ) => do
--   let (appendedCtx,T,othervars) ← elab_ident_list oldCtx newCtx vars is
--   let newVars := λ s =>
--     if s=i.getId.toString
--     then mkAppM ``V0 #[ oldCtx , T ]
--     else do
--       let old ← othervars s
--       let ID ← mkAppM ``ID #[appendedCtx]
--       let p ← mkAppM ``PROJ1 #[ID]
--       mkAppM ``SUBST_Tm #[ p , old]
--   return (appendedCtx,newVars)
-- | _ => throwUnsupportedSyntax


partial def elabGATCon_core (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (Expr × (String → MetaM Expr))
-- | `(gat_con| ⬝ ) => return (.const ``preEMPTY [] , λ _ => throwUnsupportedSyntax)
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
  let (C , restVars) ← elabGATCon_core ctx vars rest
  let (i,T) ← elabGATdecl ctx restVars d
  let res ← mkAppM ``EXTEND #[C, T]
  let newVars := λ s =>
    if s=i
    then mkAppM ``V0 #[ C , T ]
    else do
      let old ← restVars s
      let ID ← mkAppM ``ID #[res]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old]
  return (res, newVars)
| `(con_inner| $d:gat_decl ) => do
  let (i,T) ← elabGATdecl ctx vars d
  let newVars := λ s =>
    if s=i
    then mkAppM ``V0 #[ ctx , T ]
    else do
      let old ← vars s
      let ID ← mkAppM ``ID #[ctx]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old]
  let res ← mkAppM ``EXTEND #[ctx, T]
  return (res, newVars)
-- | `(gat_con| include $g:ident as ( $is:ident_list ); $rest:gat_con ) => do
--   let (newCon,newVars) ← elab_ident_list ctx (.const g.getId []) vars is
--   elabGATCon_core newCon newVars rest
| _ => throwUnsupportedSyntax


partial def elabGATCon : Syntax → MetaM Expr
| `(con_outer| ⦃  ⦄ ) => return (.const ``EMPTY [])
| `(con_outer| ⦃ $s:con_inner  ⦄ ) => do
  let (res,_) ← elabGATCon_core (.const ``EMPTY []) (λ _ => throwUnsupportedSyntax) s
  return res
| _ => throwUnsupportedSyntax

inductive nouGAT_Tm : Type where
| V : Nat → nouGAT_Tm
| nouApp : nouGAT_Tm → nouGAT_Tm → nouGAT_Tm
open nouGAT_Tm

inductive nouGAT_Ty : Type where
| nouU : nouGAT_Ty
| nouEl : nouGAT_Tm → nouGAT_Ty
| nouEq : nouGAT_Tm → nouGAT_Tm → nouGAT_Ty
| nouPi : nouGAT_Tm → nouGAT_Ty → nouGAT_Ty
open nouGAT_Ty

inductive nouGAT_Con : Type where
| nouEmpty : nouGAT_Con
| nouSingle : nouGAT_Ty → nouGAT_Con
| nouExtend : nouGAT_Con → nouGAT_Ty → nouGAT_Con
open nouGAT_Con



partial def elabnouGAT_Tm (vars : String → MetaM Expr) : Syntax → MetaM Expr
| `(gat_tm| ( $g:gat_tm ) ) => elabnouGAT_Tm vars g
| `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
      let t1 ← elabnouGAT_Tm vars g1
      let t2 ← elabnouGAT_Tm vars g2
      mkAppM ``nouApp #[t1,t2]
| `(gat_tm| $i:ident ) => do
    let n ← vars i.getId.toString
    mkAppM ``V #[n]
| _ => throwUnsupportedSyntax


partial def elabnouGAT_Arg (vars : String → MetaM Expr) : Syntax → MetaM (String × Expr)
| `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
  let t ← elabnouGAT_Tm vars g
  return (i.getId.toString,t)
| `(gat_arg| ( _ : $g:gat_tm ) ) => do
  let t ← elabnouGAT_Tm vars g
  return ("",t)
| `(gat_arg| $g:gat_tm ) => do
  let t ← elabnouGAT_Tm vars g
  return ("",t)
| _ => throwUnsupportedSyntax

partial def elabnouGAT_Ty (vars : String → MetaM Expr) : Syntax → MetaM Expr
| `(gat_ty| ( $g:gat_ty ) ) => elabnouGAT_Ty vars g
| `(gat_ty| U ) => return .const ``nouU []
| `(gat_ty| $x:gat_tm ) => do
  let t ← elabnouGAT_Tm vars x
  mkAppM ``nouEl #[t]
| `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
  let (i,domain) ← elabnouGAT_Arg vars T
  -- let elDomain ← mkAppM ``nouEl #[domain]
  let newVars := λ s =>
    if s=i
    then return .const ``zero []
    else do
      let old ← vars s
      mkAppM ``succ #[old]
  let codomain ← elabnouGAT_Ty newVars T'
  mkAppM  ``nouPi #[domain,codomain]
| `(gat_ty| $g1:gat_tm ≡ $g2:gat_tm) => do
  let t1 ← elabnouGAT_Tm vars g1
  let t2 ← elabnouGAT_Tm vars g2
  mkAppM ``nouEq #[t1,t2]
| _ => throwUnsupportedSyntax

partial def elabnouGAT_decl (vars : String → MetaM Expr) : Syntax → MetaM (String × Expr)
| `(gat_decl| $i:ident : $g:gat_ty ) => do
    let T ← elabnouGAT_Ty vars g
    return (i.getId.toString,T)
| _ => throwUnsupportedSyntax


def conSucc : Con → Nat → Nat
| EMPTY, x => x
| Γ ▷ _, x => succ (conSucc Γ x)

partial def elabnouGAT_Con (vars : String → MetaM Expr) : Syntax → MetaM (Expr × (String → MetaM Expr))
| `(con_inner| $d:gat_decl ) => do
  let (i,T) ← elabnouGAT_decl vars d
  let newVars := λ s =>
    if s=i
    then return .const ``zero []
    else do
      let old ← vars s
      mkAppM ``succ #[old]
  let res ← mkAppM ``nouSingle #[T]
  return (res, newVars)
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
  let (C , restVars) ← elabnouGAT_Con vars rest
  let (i,T) ← elabnouGAT_decl restVars d
  let res ← mkAppM ``nouExtend #[C, T]
  let newVars := λ s =>
    if s=i
    then return .const ``zero []
    else do
      let old ← restVars s
      mkAppM ``succ #[old]
  return (res, newVars)
| `(con_inner| include $g:ident as ( $is:ident_list ); $rest:con_inner ) => do
  -- let (newCon,newVars) ← elab_ident_list ctx (.const g.getId []) vars is
  let newVars := λ s => do
      let old ← vars s
      mkAppM ``conSucc #[.const g.getId [],old]
  elabnouGAT_Con newVars rest
| _ => throwUnsupportedSyntax

partial def elabnouGAT : Syntax → MetaM Expr
| `(nouGAT_instr| [nouGAT| $s ] ) => do
  let (res,_) ← elabnouGAT_Con (λ _ => throwUnsupportedSyntax) s
  return res
| `(nouGAT_instr| [nouGAT| ] ) => return .const ``nouEmpty []
| _ => throwUnsupportedSyntax


elab g:con_outer : term => elabGATCon g
elab g:nouGAT_instr : term => elabnouGAT g

def G := ⦃M : U, x : M⦄
def x := [nouGAT| include G as (_);
  N : U, y : N ]
#reduce x




























-- def v0 : preTm := prePROJ2 (preID (preEXTEND preEMPTY preUU))
-- def preAPP' (Γ : preCon) (f : preTm) (x : preTm) : preTm :=
--    preSUBST_Tm (prePAIR (preID Γ) x) (preAPP f)

-- def preCTXAPPEND (old : preCon) : preCon → preCon
-- | preEMPTY => old
-- | (preEXTEND Δ A) => preEXTEND (preCTXAPPEND old Δ) A

-- def GAT_sig : Type := preCon

-- set_option hygiene false

-- mutual
--   inductive wfCon : preCon → Prop where
--   | wfEMPTY : wfCon preEMPTY
--   | wfEXTEND : {Γ : preCon} → {A : preTy} → wfCon Γ → wfTy Γ A → wfCon (preEXTEND Γ A)

--   inductive wfSub : preCon → preCon → preSub → Prop
--   | wfEPSILON : {Γ : preCon} → {_ : wfCon Γ} → wfSub Γ preEMPTY (preEPSILON Γ)
--   | wfID : {Γ : preCon} → {_ : wfCon Γ} → wfSub Γ Γ (preID Γ)
--   | wfCOMP : {Θ Δ Γ : preCon} → {δ γ : preSub} → {_ :wfCon Θ} → {_ :wfCon Δ} → {_ : wfCon Γ} → wfSub Θ Δ δ → wfSub Δ Γ γ → wfSub Θ Γ (preCOMP γ δ)
--   | wfPAIR : {Δ Γ : preCon} → {A : preTy} → {σ : preSub} → {t : preTm} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ Γ σ → wfTm Δ (preSUBST_Ty σ A) t → wfSub Δ (preEXTEND Γ A) (prePAIR σ t)
--   | wfPROJ1 : {Δ Γ : preCon} → {A : preTy} → {τ : preSub} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ (preEXTEND Γ A) τ → wfSub Δ Γ (prePROJ1 τ)

--   inductive wfTy : preCon → preTy → Prop where
--   | wfSUBST_Ty : {Δ Γ : preCon} → {σ : preSub} → {A : preTy} → {_ : wfCon Δ} → {_ : wfCon Γ} → wfSub Δ Γ σ→ wfTy Γ A → wfTy Δ (preSUBST_Ty σ A)
--   | wfUU : {Γ : preCon} → {_ : wfCon Γ} → wfTy Γ preUU
--   | wfEL : {Γ : preCon} → {X : preTm} → {_ : wfCon Γ} → wfTm Γ preUU X → wfTy Γ (preEL X)
--   | wfPI : {Γ : preCon} → {X : preTm} → {Y : preTy} → {_ : wfCon Γ} → wfTm Γ preUU X → wfTy (preEXTEND Γ (preEL X)) Y → wfTy Γ (prePI X Y)
--   | wfEQ : {Γ : preCon} → {T : preTy} → {_ : wfCon Γ} → {_ : wfTy Γ T} → {t t' : preTm} → wfTm Γ T t → wfTm Γ T t' → wfTy Γ (preEQ t t')

--   inductive wfTm : preCon → preTy → preTm → Prop where
--   | wfSUBST_Tm : {Δ Γ : preCon} → {A : preTy} → {t : preTm} → {σ : preSub} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ Γ σ → wfTm Γ A t → wfTm Δ (preSUBST_Ty σ A) (preSUBST_Tm σ t)
--   | wfPROJ2 : {Δ Γ : preCon} → {A : preTy} → {τ : preSub} → {_ : wfCon Δ} → {_ : wfCon Γ} → {_ : wfTy Γ A} → wfSub Δ (preEXTEND Γ A) τ → wfTm Δ (preSUBST_Ty (prePROJ1 τ) A) (prePROJ2 τ)
--   | wfAPP : {Γ : preCon} → {X : preTm} → {Y : preTy} → {f : preTm} → {_ : wfCon Γ} → {_ : wfTm Γ preUU X} → {_ : wfTy (preEXTEND Γ (preEL X)) Y} → wfTm Γ (prePI X Y) f → wfTm (preEXTEND Γ (preEL X)) Y (preAPP f)
-- end

-- open wfCon wfSub wfTy wfTm

-- def Con : Type := { Γ : preCon // wfCon Γ }
-- def Subst (Δ Γ : Con) : Type := { σ : preSub // wfSub Δ.1 Γ.1 σ }
-- def Ty (Γ : Con) : Type := { A : preTy // wfTy Γ.1 A}
-- def Tm (Γ : Con) (A : Ty Γ) : Type := { t : preTm // wfTm Γ.1 A.1 t}

-- def ID {Γ : Con} : Subst Γ Γ :=
--   ⟨ preID Γ.1 , @wfID _ Γ.2 ⟩
-- def COMP {Θ Δ Γ : Con} (γ : Subst Δ Γ) (δ : Subst Θ Δ) : Subst Θ Γ :=
--   ⟨ preCOMP γ.1 δ.1 , @wfCOMP _ _ _ _ _ Θ.2 Δ.2 Γ.2 δ.2 γ.2  ⟩
-- def EMPTY : Con :=
--   ⟨ preEMPTY , wfEMPTY ⟩
-- def EPSILON {Γ : Con} : Subst Γ EMPTY :=
--   ⟨ preEPSILON Γ.1 , @wfEPSILON _ Γ.2 ⟩
-- def SUBST_Ty {Δ Γ : Con} (σ : Subst Δ Γ) (A : Ty Γ) : Ty Δ :=
--   ⟨ preSUBST_Ty σ.1 A.1 , @wfSUBST_Ty _ Γ.1 _ _ Δ.2 Γ.2 σ.2 A.2⟩
-- def SUBST_Tm {Δ Γ : Con} {A : Ty Γ} (σ : Subst Δ Γ) (t : Tm Γ A) : Tm Δ (SUBST_Ty σ A) :=
--   ⟨ preSUBST_Tm σ.1 t.1 , @wfSUBST_Tm _ Γ.1 _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2 ⟩

-- def EXTEND (Γ : Con) (A : Ty Γ) : Con :=
--   ⟨ preEXTEND Γ.1 A.1 , @wfEXTEND _ _ Γ.2 A.2 ⟩
-- def PAIR {Δ Γ : Con} {A : Ty Γ} (σ : Subst Δ Γ) (t : Tm Δ (SUBST_Ty σ A)) : Subst Δ (EXTEND Γ A) :=
--   ⟨ prePAIR σ.1 t.1 , @wfPAIR _ _ _ _ _ Δ.2 Γ.2 A.2 σ.2 t.2⟩
-- def PROJ1 {Δ Γ : Con} {A : Ty Γ} (τ : Subst Δ (EXTEND Γ A)) : Subst Δ Γ :=
--   ⟨ prePROJ1 τ.1 , @wfPROJ1 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩
-- def PROJ2 {Δ Γ : Con} {A : Ty Γ} (τ : Subst Δ (EXTEND Γ A)) : Tm Δ (SUBST_Ty (PROJ1 τ) A) :=
--   ⟨ prePROJ2 τ.1 , @wfPROJ2 _ _ A.1 _ Δ.2 Γ.2 A.2 τ.2 ⟩

-- def UU {Γ : Con} : Ty Γ :=
--   ⟨ preUU , @wfUU Γ.1 Γ.2 ⟩
-- def EL {Γ : Con} (X : Tm Γ UU) : Ty Γ :=
--   ⟨ preEL X.1 , @wfEL _ _ Γ.2 X.2⟩
-- def PI {Γ : Con} (X : Tm Γ UU) (Y : Ty (EXTEND Γ (EL X))) : Ty Γ :=
--   ⟨ prePI X.1 Y.1 , @wfPI _ _ _ Γ.2 X.2 Y.2⟩
-- def APP {Γ : Con} {X : Tm Γ UU} {Y : Ty (EXTEND Γ (EL X))} (f : Tm Γ (PI X Y)) : Tm (EXTEND Γ (EL X)) Y :=
--   ⟨ preAPP f.1, @wfAPP _ _ _ _ Γ.2 X.2 Y.2 f.2 ⟩





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
