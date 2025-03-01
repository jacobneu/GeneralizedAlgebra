import GeneralizedAlgebra.signature
import Lean

open Lean Elab Meta
open Con Subst Ty Tm

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

declare_syntax_cat con_named
syntax "[namedGAT|" con_inner "]" : con_named

inductive Arg : Type where
| Impl : String → Expr → Arg
| Expl : String → Expr → Arg
| Anon : Expr → Arg
open Arg
def extractTy : Arg → Expr
| Impl _ e => e
| Expl _ e => e
| Anon e => e

def argMatch (key : String) : Arg → Bool
| Impl i _ => key=i
| Expl i _ => key=i
| Anon _ => false

def argToString : Arg → String
| Impl i _ => "{" ++ i ++ "}"
| Expl i _ => "(" ++ i ++ ")"
| Anon _ => "*"

def argEl : Arg → MetaM Arg
| Impl i t => do
    let T ← mkAppM ``EL #[t]
    return (Impl i T)
| Expl i t => do
    let T ← mkAppM ``EL #[t]
    return (Expl i T)
| Anon t => do
    let T ← mkAppM ``EL #[t]
    return (Anon T)

structure varStruct where
  (f : String → MetaM Expr)
  (topnames : List String)
  (telescopes : List (List Arg))

structure varTel (VV : varStruct) where
  (f : String → MetaM Expr)
  (args : List Arg)

def varLookup (VV : varStruct) (key : String) : MetaM Expr
:= VV.f key

def varExtend (VV : varStruct) (key : String) (ctx : Expr) (newType : Expr) (newCtx : Expr) (newTelescope : List Arg): varStruct :=
⟨ λ s =>
    if s=key
    then mkAppM ``V0 #[ ctx , newType ]
    else do
      let old ← varLookup VV s
      let ID ← mkAppM ``ID #[newCtx]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old],
  VV.topnames ++ [key],
  VV.telescopes ++ [newTelescope]
⟩

def varEmpty : varStruct := ⟨ λ s => throwError ("Unknown var: " ++ s), [], [] ⟩

def varTelEmpty (VV : varStruct) : varTel VV := ⟨ VV.f , [] ⟩

def varTelLookup {VV : varStruct} (TT : varTel VV) (key : String) :=
  TT.f key

def varTelExtend {VV : varStruct} (TT : varTel VV) (newArg : Arg) (ctx : Expr)  (newCtx : Expr) : varTel VV :=
⟨ λ s =>
    if argMatch s newArg
    then mkAppM ``V0 #[ ctx , extractTy newArg ]
    else do
      let old ← varTelLookup TT s
      let ID ← mkAppM ``ID #[newCtx]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old],
  TT.args ++ [newArg],
⟩


#check mkListLit

partial def elabGATTm {vars : varStruct} (ctx : Expr) (TT : varTel vars) : Syntax → MetaM Expr
| `(gat_tm| ( $g:gat_tm ) ) => elabGATTm ctx TT g
| `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
      let t1 ← elabGATTm ctx TT g1
      let Appt1 ← mkAppM ``APP #[t1]
      let t2 ← elabGATTm ctx TT g2
      let ID ← mkAppM ``ID #[ctx]
      let substt2 ← mkAppM ``PAIR #[ID,t2]
      mkAppM ``SUBST_Tm #[substt2,Appt1]
| `(gat_tm| $i:ident ) => varTelLookup TT i.getId.toString
| _ => throwError "TmFail"


partial def elabGATArg {vars : varStruct} (ctx : Expr) (TT : varTel vars) : Syntax → MetaM Arg
| `(gat_arg| { $i:ident : $g:gat_tm } ) => do
  let t ← elabGATTm ctx TT g
  return (Impl i.getId.toString t)
| `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
  let t ← elabGATTm ctx TT g
  return (Expl i.getId.toString t)
| `(gat_arg| ( _ : $g:gat_tm ) ) => do
  let t ← elabGATTm ctx TT g
  return (Anon t)
| `(gat_arg| $g:gat_tm ) => do
  let t ← elabGATTm ctx TT g
  return (Anon t)
| _ => throwError "ArgFail"


partial def elabGATTy {vars : varStruct} (ctx : Expr) (TT : varTel vars) : Syntax → MetaM (varTel vars × Expr)
| `(gat_ty| ( $g:gat_ty ) ) => elabGATTy ctx TT g
| `(gat_ty| U ) => return (TT, .const ``UU [])
| `(gat_ty| $x:gat_tm ) => do
  let t ← elabGATTm ctx TT x
  let T ← mkAppM ``EL #[t]
  return (TT, T)
| `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
  let argT ← elabGATArg ctx TT T
  let domain := extractTy argT
  let elDomain ← mkAppM ``EL #[domain]
  let elT ← argEl argT
  let newCtx ← mkAppM ``EXTEND #[ctx,elDomain]
  let newTT := varTelExtend TT elT ctx newCtx
  let (newnewTT,codomain) ← elabGATTy newCtx newTT T'
  let result ← mkAppM  ``PI #[domain,codomain]
  return (newnewTT,result)
| `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
  let tt1 ← elabGATTm ctx TT t1
  let tt2 ← elabGATTm ctx TT t2
  let T ← mkAppM ``EQ #[tt1,tt2]
  return (TT,T)
| _ => throwError "TyFail"

partial def elabGATdecl (ctx : Expr) (vars : varStruct) : Syntax → MetaM (String × Expr × varTel vars)
| `(gat_decl| $i:ident : $g:gat_ty ) => do
    let (TT,T) ← elabGATTy ctx (varTelEmpty vars) g
    return (i.getId.toString,T,TT)
| _ => throwError "declFail"


partial def elabGATCon_core (ctx : Expr) (vars : varStruct) : Syntax → MetaM (Expr × varStruct)
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
  let (C , restVars) ← elabGATCon_core ctx vars rest
  let (i,T,TT) ← elabGATdecl ctx restVars d
  let newCtx ← mkAppM ``EXTEND #[C, T]
  let newVars := varExtend restVars i C T newCtx (TT.args)
  return (newCtx, newVars)
| `(con_inner| $d:gat_decl ) => do
  let (i,T,TT) ← elabGATdecl ctx vars d
  let newCtx ← mkAppM ``EXTEND #[ctx, T]
  let newVars := varExtend vars i ctx T newCtx (TT.args)
  let res ← mkAppM ``EXTEND #[ctx, T]
  return (res, newVars)
-- | `(gat_con| include $g:ident as ( $is:ident_list ); $rest:gat_con ) => do
--   let (newCon,newVars) ← elab_ident_list ctx (.const g.getId []) vars is
--   elabGATCon_core newCon newVars rest
| _ => throwError "Con_coreFail"


partial def elabGATCon : Syntax → MetaM Expr
| `(con_outer| ⦃  ⦄ ) => return (.const ``EMPTY [])
| `(con_outer| ⦃ $s:con_inner  ⦄ ) => do
  let (res,_) ← elabGATCon_core (.const ``EMPTY []) varEmpty s
  return res
| _ => throwError "ConFail"


def mkListStrLit : List String → MetaM Expr :=
  (mkListLit (.const `String [])) ∘ (List.map mkStrLit)

-- def mkArgLit : Arg → MetaM Expr
-- | Impl i t => return mkStrLit $ "{" ++ i ++ "}" --mkAppM `Arg.Impl #[mkStrLit i,t]
-- | Expl i t => return mkStrLit $ "(" ++ i ++ ")" --mkAppM `Arg.Expl #[mkStrLit i,t]
-- | Anon t => return mkStrLit $ "@" --mkAppM `Arg.Anon #[t]

-- def mkListArgLit (L : List Arg) : MetaM Expr :=
--   List.mapM mkArgLit L >>= mkListLit (.const `Arg [])

-- def mkListArgLit (L : List Arg) : MetaM Expr :=
--   List.mapM mkArgLit L >>= mkListLit (.const `String [])

-- def LArg := List Arg
-- def LStr := List String

-- def mkListListArgLit (LL : List (List Arg)) : MetaM Expr :=
--   List.mapM mkListArgLit LL >>=  mkListLit (.const `LArg [])

-- def mkListListArgLit (LL : List (List Arg)) : MetaM Expr :=
--   List.mapM mkListArgLit LL >>=  mkListLit (.const `String [])

partial def elabnamedGAT : Syntax → MetaM Expr
| `(con_outer| ⦃  ⦄ ) => return (.const ``EMPTY [])
| `(con_named| [namedGAT| $s:con_inner ] ) => do
  let (resCon,VV) ← elabGATCon_core (.const ``EMPTY []) varEmpty s
  let topList ← mkListStrLit VV.topnames
  let telescopes ← mkListStrLit (List.map argToString (List.join VV.telescopes))
  mkAppM ``mk3 #[resCon,topList,telescopes]
| _ => throwError "namedGATFail"


elab g:con_outer : term => elabGATCon g
elab g:con_named : term => elabnamedGAT g
