import GeneralizedAlgebra.signature
import Lean

open Lean Elab Meta
open Ty Tm

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
syntax "{" ident ":" gat_tm "}" : gat_arg
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
    let T ← mkAppM ``EL #[t]
    return (metaImpl i T)
| metaExpl i t => do
    let T ← mkAppM ``EL #[t]
    return (metaExpl i T)
| metaAnon t => do
    let T ← mkAppM ``EL #[t]
    return (metaAnon T)

structure varStruct where
  (f : String → MetaM Expr)
  (topnames : List String)
  (telescopes : List (List metaArg × Expr))
  (getArgs : String → MetaM (List metaArg))

structure varTel (VV : varStruct) where
  (f : String → MetaM Expr)
  (args : List metaArg)

def varLookup (VV : varStruct) (key : String) : MetaM Expr
:= VV.f key

#check mkNatLit

def varExtend (VV : varStruct) (key : String) (ctx : Expr) (newType : Expr) (newCtx : Expr) (newTelescope : List metaArg) (resT : Expr): varStruct :=
⟨ λ s =>
    if s=key
    then mkAppM ``VAR #[ mkNatLit 0 ]
    else do
      let old ← varLookup VV s
      -- let ID ← mkAppM ``ID #[newCtx]
      -- let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``WkTm #[ old ],
  VV.topnames ++ [key],
  VV.telescopes ++ [(newTelescope,resT)],
  λ s => if s=key then return newTelescope else VV.getArgs s
⟩

def varEmpty : varStruct := ⟨ λ s => throwError ("Unknown var: " ++ s), [], [], λ s => throwError ("Can't get args for unknown var: " ++ s) ⟩

def varTelEmpty (VV : varStruct) : varTel VV := ⟨ VV.f , [] ⟩

def varTelLookup {VV : varStruct} (TT : varTel VV) (key : String) : MetaM (Expr × List metaArg) := do
  let T ← TT.f key
  let args ← (VV.getArgs key) <|> return []
  return (T,args)

def varTelExtend {VV : varStruct} (TT : varTel VV) (newArg : metaArg) (ctx : Expr)  (newCtx : Expr) : varTel VV :=
⟨ λ s =>
    if argMatch s newArg
    then mkAppM ``VAR #[ mkNatLit 0 ]
    else do
      let (old,_) ← varTelLookup TT s
      mkAppM ``WkTm #[ old ],
  TT.args ++ [newArg],
⟩

partial def splitArgList (message : String) : List metaArg → MetaM (metaArg × List metaArg)
| [] => throwError message
| (metaExpl i e)::As => return (metaExpl i e,As)
| (metaImpl _ _)::As => splitArgList message As
| (metaAnon e)::As => return (metaAnon e,As)

partial def failIfExplicitArgs (message : String) : List metaArg → MetaM Unit
| [] => return ()
| (metaExpl _ _)::_ => throwError message
| (metaImpl _ _)::As => failIfExplicitArgs message As
| (metaAnon _)::_ => throwError message

partial def elabGATTm {vars : varStruct} (ctx : Expr) (TT : varTel vars) : Syntax → MetaM (Expr × List metaArg)
| `(gat_tm| ( $g:gat_tm ) ) => elabGATTm ctx TT g
| `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
      let (t1,args1) ← elabGATTm ctx TT g1
      let (A,args1') ← splitArgList "Too many args #0" args1
      let domain := extractMetaTy A
--         -- TODO: Check the type of A against the type of t2
      -- let Appt1 ← mkAppM ``APP #[t1]
      let (t2,args2)← elabGATTm ctx TT g2
      failIfExplicitArgs "Insufficient Args #0" args2
--       -- let actualT2 ← reduce t2
--       -- let expectedT2 ← reduce (extractMetaTy A)
--       -- let tyMatch ← isDefEq actualT2 expectedT2
--       -- if (not tyMatch) then
--       --   throwError "X"
--       -- else do
--       let ID ← mkAppM ``ID #[ctx]
--       let substt2 ← mkAppM ``PAIR #[ID,t2]
      let resT ← mkAppM ``APP #[t1,domain,t1,t2]
      return (resT,args1')
| `(gat_tm| $i:ident ) => do
      varTelLookup TT i.getId.toString
      -- let args ← vars.getArgs i.getI
| _ => throwError "TmFail"


partial def elabClosedGATTm {vars : varStruct} (ctx : Expr) (TT : varTel vars) (s : Syntax) : MetaM Expr := do
  let (T,args) ← elabGATTm ctx TT s
  failIfExplicitArgs "Insufficient Args #1" args
  return T

partial def elabGATArg {vars : varStruct} (ctx : Expr) (TT : varTel vars) : Syntax → MetaM metaArg
| `(gat_arg| { $i:ident : $g:gat_tm } ) => do
  let t ← elabClosedGATTm ctx TT g
  return (metaImpl i.getId.toString t)
| `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
  let t ← elabClosedGATTm ctx TT g
  return (metaExpl i.getId.toString t)
| `(gat_arg| ( _ : $g:gat_tm ) ) => do
  let t ← elabClosedGATTm ctx TT g
  return (metaAnon t)
| `(gat_arg| $g:gat_tm ) => do
  let t ← elabClosedGATTm ctx TT g
  return (metaAnon t)
| _ => throwError "ArgFail"


partial def elabGATTy {vars : varStruct} (ctx : Expr) (TT : varTel vars) : Syntax → MetaM (varTel vars × Expr × Expr)
-- | `(gat_ty| ( $g:gat_ty ) ) => elabGATTy ctx TT g
| `(gat_ty| U ) => return (TT, .const ``UU [], .const ``UU [])
| `(gat_ty| $x:gat_tm ) => do
  let t ← elabClosedGATTm ctx TT x
  let T ← mkAppM ``EL #[t]
  return (TT, T, T)
| `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
  let argT ← elabGATArg ctx TT T
  let domain := extractMetaTy argT
  let elDomain ← mkAppM ``EL #[domain]
  let elT ← argEl argT
  let newCtx ← mkAppM ``EXTEND #[ctx,elDomain]
  let newTT := varTelExtend TT elT ctx newCtx
  let (newnewTT,codomain,resT) ← elabGATTy newCtx newTT T'
  let result ← mkAppM  ``PI #[domain,codomain]
  return (newnewTT,result,resT)
| `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
  let tt1 ← elabClosedGATTm ctx TT t1
  let tt2 ← elabClosedGATTm ctx TT t2
  let T ← mkAppM ``EQ #[tt1,tt2]
  return (TT,T,T)
| _ => throwError "TyFail"

partial def elabGATdecl (ctx : Expr) (vars : varStruct) : Syntax → MetaM (String × varTel vars × Expr × Expr)
| `(gat_decl| $i:ident : $g:gat_ty ) => do
    let (TT,T,resT) ← elabGATTy ctx (varTelEmpty vars) g
    return (i.getId.toString,TT,T,resT)
| _ => throwError "declFail"


partial def elabGATCon_core (ctx : Expr) (vars : varStruct) : Syntax → MetaM (Expr × varStruct)
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
  let (C , restVars) ← elabGATCon_core ctx vars rest
  let (i,TT,T,resT) ← elabGATdecl ctx restVars d
  let newCtx ← mkAppM ``EXTEND #[C, T]
  let newVars := varExtend restVars i C T newCtx TT.args resT
  return (newCtx, newVars)
| `(con_inner| $d:gat_decl ) => do
  let (i,TT,T,resT) ← elabGATdecl ctx vars d
  let newCtx ← mkAppM ``EXTEND #[ctx,T]
  let newVars := varExtend vars i ctx T newCtx TT.args resT
  let res ← mkAppM ``EXTEND #[ctx,T]
  return (res, newVars)
-- | `(gat_con| include $g:ident as ( $is:ident_list ); $rest:gat_con ) => do
--   let (newCon,newVars) ← elab_ident_list ctx (.const g.getId []) vars is
--   elabGATCon_core newCon newVars rest
| _ => throwError "Con_coreFail"




def LStr := List String
def mkListStrLit : List String → MetaM Expr :=
  (mkListLit (.const `String [])) ∘ (List.map mkStrLit)

def mkListListStrLit (LL : List (List String)) : MetaM Expr :=
  List.mapM mkListStrLit LL >>= mkListLit (.const `LStr [])



-- def mkListArgLit (L : List Arg) : MetaM Expr :=
--   List.mapM mkArgLit L >>= mkListLit (.const `String [])

def LArg := List Arg × Ty

def mkArgLit : metaArg → MetaM Expr
| metaImpl i t => mkAppM `Arg.Impl #[mkStrLit i,t]
| metaExpl i t => mkAppM `Arg.Expl #[mkStrLit i,t]
| metaAnon t => mkAppM `Arg.Anon #[t]

def mkListArgLit (tele : List metaArg × Expr) : MetaM Expr := do
  let teleArgs ← List.mapM mkArgLit tele.1
  let teleExpr ← mkListLit (.const `Arg []) teleArgs
  mkAppM ``Prod.mk #[teleExpr,tele.2]

def mkListListArgLit (LL : List (List metaArg × Expr)) : MetaM Expr :=
  List.mapM mkListArgLit LL >>=  mkListLit (.const `LArg [])

partial def elabGATCon : Syntax → MetaM Expr
| `(con_outer| ⦃  ⦄ ) => do
  let emptyStrList ← mkListStrLit []
  let emptyLArgList ← mkListListArgLit []
  mkAppM ``GATdata.mk  #[.const ``EMPTY [],emptyStrList,emptyLArgList]
| `(con_outer| ⦃ $s:con_inner  ⦄ ) => do
  let (resCon,VV) ← elabGATCon_core (.const ``EMPTY []) varEmpty s
  let topList ← mkListStrLit VV.topnames
  let telescopes ← mkListListArgLit VV.telescopes
  mkAppM ``GATdata.mk #[resCon,topList,telescopes]
| _ => throwError "ConFail"


elab g:con_outer : term => elabGATCon g
