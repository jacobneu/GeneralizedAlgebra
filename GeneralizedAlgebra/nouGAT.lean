import GeneralizedAlgebra.typecheck
import Lean

open Lean Elab Meta
open preTy preTm

declare_syntax_cat gat_ty
syntax "U"       : gat_ty
syntax "(" gat_ty ")" : gat_ty

declare_syntax_cat gat_tm
syntax ident     : gat_tm
syntax "(" gat_tm ")" : gat_tm
syntax:60 gat_tm:60 gat_tm:61 : gat_tm
syntax:58 gat_tm:58  "#⟨" gat_tm:59 "⟩" : gat_tm
syntax gat_tm : gat_ty
syntax gat_tm " ≡ " gat_tm : gat_ty

declare_syntax_cat gat_decl
syntax ident ":" gat_ty : gat_decl

declare_syntax_cat gat_arg
syntax "(" ident ":" gat_tm ")" : gat_arg
syntax "(" "_" ":" gat_tm ")" : gat_arg
-- syntax "{" ident ":" gat_tm "}" : gat_arg
syntax gat_tm : gat_arg

syntax gat_arg "⇒" gat_ty : gat_ty


-- declare_syntax_cat ident_list
-- syntax ident : ident_list
-- syntax "_" : ident_list
-- syntax ident_list "," "_" : ident_list
-- syntax ident_list "," ident : ident_list

declare_syntax_cat con_inner
syntax gat_decl : con_inner
syntax con_inner "," gat_decl : con_inner
-- syntax "include" ident "as" "(" ident_list ");" con_inner : con_inner
-- declare_syntax_cat con_outer
-- syntax "⦃" "⦄" : con_outer
-- syntax "⦃" con_inner "⦄" : con_outer

declare_syntax_cat condata_outer
syntax "[GATdata|" "]" : condata_outer
syntax "[GATdata|" con_inner "]" : condata_outer


inductive metaArg : Type where
| metaImpl : String → Expr → metaArg
| metaExpl : String → Expr → metaArg
| metaAnon : Expr → metaArg
open metaArg
def extractMetaTy : metaArg → Expr
| metaImpl _ e => e
| metaExpl _ e => e
| metaAnon e => e

def argMatch (key : String) : metaArg → Bool
| metaImpl i _ => key=i
| metaExpl i _ => key=i
| metaAnon _ => false


def argEl : metaArg → MetaM metaArg
| metaImpl i t => do
    let T ← mkAppM ``preEL #[t]
    return (metaImpl i T)
| metaExpl i t => do
    let T ← mkAppM ``preEL #[t]
    return (metaExpl i T)
| metaAnon t => do
    let T ← mkAppM ``preEL #[t]
    return (metaAnon T)

def argRecord
| metaImpl i _ => "Impl(" ++ i ++ ")"
| metaExpl i _ => "Expl("++ i ++ ")"
| metaAnon _ => "Anon"

structure varStruct where
  (lkup : String → String → MetaM Nat)
  (topnames : List String)
  (telescopes : List (List metaArg × Expr))

open Nat

partial def getN {A : Type} (message : String) : List A → Nat → MetaM A
| [], _ => throwError message
| x::_, 0 => return x
| _::xs, succ n => getN message xs n

def getArgs (VV : varStruct) (key : String) : MetaM (List metaArg) :=
    Prod.fst <$> (VV.lkup key "" >>= getN ("Error: getArgs failed on variable \"" ++ key ++ "\"") VV.telescopes)

def getExpr (VV : varStruct) (key : String) : MetaM Expr :=
    Prod.snd <$> (VV.lkup key "" >>= getN ("Error: getExpr failed on variable \"" ++ key ++ "\"") VV.telescopes)

def getLength (VV : varStruct) : Nat := List.length (VV.topnames)

def varExtend (VV : varStruct) (key : String) (newTelescope : List metaArg) (resT : Expr): varStruct :=
  ⟨
    λ s mess => if s=key then return 0 else succ <$> VV.lkup s (mess ++ "tried1 \"" ++ key ++ "\" vs. \"" ++  s ++ "\"; "),
    key::VV.topnames,
    (newTelescope,resT)::VV.telescopes
  ⟩

def varEmpty : varStruct := ⟨ λ s mess => throwError ("Unknown var: " ++ s ++ ". Info dump:" ++ mess), [], [] ⟩


def varTelLkup (VV : varStruct) : List metaArg → String → String → MetaM Nat
| [], key, message => VV.lkup key message
| a::rest, key, message =>
  if argMatch key a
  then return 0
  else succ <$> varTelLkup VV rest key (message ++ "tried2 \"" ++ argRecord a ++ "\"; ")

-- partial def splitArgList (message : String) : List metaArg → MetaM (metaArg × List metaArg)
-- | [] => throwError message
-- | (metaExpl i e)::As => return (metaExpl i e,As)
-- | (metaImpl _ _)::As => splitArgList message As
-- | (metaAnon e)::As => return (metaAnon e,As)

-- partial def failIfExplicitArgs (message : String) : List metaArg → MetaM Unit
-- | [] => return ()
-- | (metaExpl _ _)::_ => throwError message
-- | (metaImpl _ _)::As => failIfExplicitArgs message As
-- | (metaAnon _)::_ => throwError message

partial def elabGATTm (TT : List metaArg) (vars : varStruct)  : Syntax → MetaM Expr
| `(gat_tm| ( $g:gat_tm ) ) => elabGATTm TT vars g
| `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
      let t1 ← elabGATTm TT vars g1
      -- let (_,args1') ← splitArgList "Too many args #0" args1
      -- let domain := extractMetaTy A
--         -- TODO: Check the type of A against the type of t2
      -- let Appt1 ← mkAppM ``APP #[t1]
      let t2 ← elabGATTm TT vars g2
      -- failIfExplicitArgs "Insufficient Args #0" args2
--       -- let actualT2 ← reduce t2
--       -- let expectedT2 ← reduce (extractMetaTy A)
--       -- let tyMatch ← isDefEq actualT2 expectedT2
--       -- if (not tyMatch) then
--       --   throwError "X"
--       -- else do
--       let ID ← mkAppM ``ID #[ctx]
--       let substt2 ← mkAppM ``PAIR #[ID,t2]
      let resT ← mkAppM ``preAPP #[t1,t2]
      return resT
| `(gat_tm| $i:ident ) => do
      let b ← varTelLkup vars TT i.getId.toString ("Lookup \"" ++ i.getId.toString ++ "\"; ")
      mkAppM ``preVAR #[mkNatLit b]
| `(gat_tm| $g1 #⟨ $g2 ⟩ ) => do
      let t1 ← elabGATTm TT vars g1
      let t2 ← elabGATTm TT vars g2
      -- failIfExplicitArgs "Insufficient Args #2" args2
      let resT ← mkAppM ``preTRANSP #[t2,t1]
      return resT

| _ => throwError "TmFail"


-- returns the preTm
partial def elabClosedGATTm (TT : List metaArg) (vars : varStruct)  (s : Syntax) : MetaM Expr := do
  let t ← elabGATTm TT vars s
  -- failIfExplicitArgs "Insufficient Args #1" args
  return t

partial def elabGATArg (TT : List metaArg) (vars : varStruct) : Syntax → MetaM metaArg
-- | `(gat_arg| { $i:ident : $g:gat_tm } ) => do
--   let t ← elabClosedGATTm ctx TT g
--   return (metaImpl i.getId.toString t)
| `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
  let t ← elabClosedGATTm TT vars g
  return (metaExpl i.getId.toString t)
| `(gat_arg| ( _ : $g:gat_tm ) ) => do
  let t ← elabClosedGATTm TT vars g
  return (metaAnon t)
| `(gat_arg| $g:gat_tm ) => do
  let t ← elabClosedGATTm TT vars g
  return (metaAnon t)
| _ => throwError "ArgFail"

-- returns (the preTy, the telescope)
partial def elabGATTy (TT : List metaArg) (vars : varStruct)  : Syntax → MetaM (Expr × List metaArg)
| `(gat_ty| U ) => return (.const ``preUU [],TT)
| `(gat_ty| $x:gat_tm ) => do
  let t ← elabClosedGATTm TT vars x
  let T ← mkAppM ``preEL #[t]
  return (T, TT)
| `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
  let argT ← elabGATArg TT vars T
  let domain := extractMetaTy argT
  -- let elDomain ← mkAppM ``preEL #[domain]
  -- let elT ← argEl argT
  -- let newCtx ← mkAppM ``preEXTEND #[ctx,elDomain]
  -- let newTT := varExtend TT "" [elT]
  -- let (newnewTT,codomain,resT) ← elabGATTy newTT newCtx  T'
  let (codomain,newTT) ← elabGATTy (argT::TT) vars T'
  let result ← mkAppM  ``prePI #[domain,codomain]
  return (result,newTT)
| `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
  let tt1 ← elabClosedGATTm TT vars t1
  let tt2 ← elabClosedGATTm TT vars t2
  let T ← mkAppM ``preEQ #[tt1,tt2]
  return (T,TT)
| _ => throwError "TyFail"

-- returns (the preTy, the topname, the telescope)
partial def elabGATdecl (vars : varStruct) : Syntax → MetaM (Expr × String × List metaArg)
| `(gat_decl| $i:ident : $g:gat_ty ) => do
    let (T,TT) ← elabGATTy [] vars g
    return (T,i.getId.toString,TT)
| _ => throwError "declFail"


partial def elabGATCon_core : Syntax → MetaM (Expr × varStruct)
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
  let (restCon , restVars) ← elabGATCon_core rest
  let (T,i,TT) ← elabGATdecl restVars d
  let newCtx ← mkAppM ``preEXTEND #[restCon, T]
  let newVars := varExtend restVars i TT T
  return (newCtx, newVars)
| `(con_inner| $d:gat_decl ) => do
  let (T,i,TT) ← elabGATdecl varEmpty d
  let newCtx ← mkAppM ``preEXTEND #[.const ``preEMPTY [],T]
  let newVars := varExtend varEmpty i TT T
  return (newCtx, newVars)
-- | `(gat_con| include $g:ident as ( $is:ident_list ); $rest:gat_con ) => do
--   let (newCon,newVars) ← elab_ident_list ctx (.const g.getId []) vars is
--   elabGATCon_core newCon newVars rest
| _ => throwError "Con_coreFail"


def type0 := Type 0
def type1 := Type 1
def lev0 : Level := Lean.Level.zero
def lev1 : Level := Lean.Level.succ lev0
def consttype0 : type0 → type1 := λ _ => type0
def el1 (X : Type 0) : Type 1 :=
  PUnit.{2} → X
-- def SigmaExpl {u v} A B := @Sigma u v A B
-- #check mkAppN

partial def elabAlgTy (algΓ : Expr) : Syntax → MetaM (Expr × Level)
| `(gat_decl| $_:ident : U ) => return (.lam `_ algΓ (.const ``type0 []) .default,lev1)
| `(gat_decl| $_:ident : $_:gat_tm ) => return (.lam `_ algΓ (.bvar 0) .default,lev0)
-- | `(gat_decl| $_:ident : $x:gat_tm ) => return (.lam `_ algΓ (.app (.const ``el1 []) $ .bvar 0) .default)
-- | `(gat_decl| $_:ident : $T:gat_arg ⇒ $T':gat_ty) => _
-- | `(gat_decl| $_:ident : $t1:gat_tm ≡ $t2:gat_tm) => _
| _ => return (.lam `_ algΓ (.const ``type0 []) .default,lev1)
-- | _ => throwError "AlgTyFail"

partial def elabAlgCon : Syntax → MetaM Expr
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
    let algΓ ← elabAlgCon rest
    let (algA,levA) ← elabAlgTy algΓ d
    return (mkApp2 (.const ``Sigma [lev1,levA]) algΓ algA)
| `(con_inner| $_:gat_decl ) => return .const ``type0 []
| _ => throwError "Alg_coreFail"


def LStr := List String
def mkListStrLit : List String → MetaM Expr :=
  (mkListLit (.const `String [])) ∘ (List.map mkStrLit)

def mkListListStrLit (LL : List (List String)) : MetaM Expr :=
  List.mapM mkListStrLit LL >>= mkListLit (.const `LStr [])


def LArg := List preArg × preTy

def mkArgLit : metaArg → MetaM Expr
| metaImpl i t => mkAppM `preArg.preImpl #[mkStrLit i,t]
| metaExpl i t => mkAppM `preArg.preExpl #[mkStrLit i,t]
| metaAnon t => mkAppM `preArg.preAnon #[t]

def mkListArgLit (tele : List metaArg × Expr) : MetaM Expr := do
  let teleArgs ← List.mapM mkArgLit tele.1
  let teleExpr ← mkListLit (.const `preArg []) teleArgs
  mkAppM ``Prod.mk #[teleExpr,tele.2]

def mkListListArgLit (LL : List (List metaArg × Expr)) : MetaM Expr :=
  List.mapM mkListArgLit LL >>=  mkListLit (.const `LArg [])

--
  -- def mkPreTmLit : preTm → Expr
  -- | preVAR n => .app (.const `preVAR []) (mkNatLit n)
  -- | preAPP f t => mkApp2 (.const `preAPP []) (mkPreTmLit f) (mkPreTmLit t)
  -- | preTRANSP f t => mkApp2 (.const `preTRANSP []) (mkPreTmLit f) (mkPreTmLit t)

  -- def mkPreTyLit : preTy → Expr
  -- | preUU => .const `preUU []
  -- | preEQ s t => mkApp2 (.const `preEQ []) (mkPreTmLit s) (mkPreTmLit t)
  -- | prePI X Y => mkApp2 (.const `prePI []) (mkPreTmLit X) (mkPreTyLit Y)
  -- | preEL X => .app (.const `prePI []) (mkPreTmLit X)

-- def mkPreConLit : preCon → Expr
-- | [] => mkApp (mkConst ``List.nil [Lean.Level.zero]) (.const `preTy [])
-- | A::Γ => mkApp3 (mkConst ``List.cons [Lean.Level.zero]) (.const `preTy []) (mkPreTyLit A) (mkPreConLit Γ)


partial def elabGATConData : Syntax → MetaM Expr
| `(condata_outer| [GATdata| ] ) => do
  let emptyStrList ← mkListStrLit []
  let emptyLArgList ← mkListListArgLit []
  let res ← mkAppM ``GATdata.mk  #[.const ``preEMPTY [],emptyStrList,emptyLArgList]
  return res
  -- mkAppM ``Prod.mk #[res,.const ``Empty []]
| `(condata_outer| [GATdata| $s:con_inner ] ) => do
  let (resCon,VV) ← elabGATCon_core s
  let topList ← mkListStrLit $ VV.topnames
  let telescopes ← mkListListArgLit $ List.map (λ (l,t) => (List.reverse l,t)) VV.telescopes
  let res ← mkAppM ``GATdata.mk #[resCon,topList,telescopes]
  return res
  -- let alg ← elabAlgCon s
  -- mkAppM ``Prod.mk #[res,alg]
| _ => throwError "ConFail"

-- elab g:con_outer : term => elabGATCon g

elab g:condata_outer : term => elabGATConData g
