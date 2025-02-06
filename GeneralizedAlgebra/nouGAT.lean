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


partial def elabGATTy (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (Expr × Expr)
| `(gat_ty| ( $g:gat_ty ) ) => elabGATTy ctx vars g
| `(gat_ty| U ) => return (.const ``stringNil [], .const ``UU [])
| `(gat_ty| $x:gat_tm ) => do
  let t ← elabGATTm ctx vars x
  let T ← mkAppM ``EL #[t]
  return (.const ``stringNil [], T)
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
  let (codNames,codomain) ← elabGATTy newCtx newVars T'
  let result ← mkAppM  ``PI #[domain,codomain]
  let Tnames ← mkAppM ``stringCons #[mkStrLit i,codNames]
  return (Tnames,result)
| `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
  let tt1 ← elabGATTm ctx vars t1
  let tt2 ← elabGATTm ctx vars t2
  let T ← mkAppM ``EQ #[tt1,tt2]
  return (.const ``stringNil [],T)
| _ => throwUnsupportedSyntax

partial def elabGATdecl (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (String × Expr × Expr)
| `(gat_decl| $i:ident : $g:gat_ty ) => do
    let (Tnames,T) ← elabGATTy ctx vars g
    return (i.getId.toString,Tnames,T)
| _ => throwUnsupportedSyntax


partial def elabGATCon_core (ctx : Expr) (vars : String → MetaM Expr) : Syntax → MetaM (Expr × Expr × Expr × (String → MetaM Expr))
-- | `(gat_con| ⬝ ) => return (.const ``preEMPTY [] , λ _ => throwUnsupportedSyntax)
| `(con_inner| $rest:con_inner , $d:gat_decl ) => do
  let (C , restNames, topnames, restVars) ← elabGATCon_core ctx vars rest
  let (i,Tnames,T) ← elabGATdecl ctx restVars d
  let res ← mkAppM ``EXTEND #[C, T]
  let newVars := λ s =>
    if s=i
    then mkAppM ``V0 #[ C , T ]
    else do
      let old ← restVars s
      let ID ← mkAppM ``ID #[res]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old]
  let newNames ← mkAppM ``List.append #[restNames,Tnames]
  let newNames' ← mkAppM ``snoc #[newNames, mkStrLit i]
  let newTopnames ← mkAppM ``snoc #[topnames, mkStrLit i]
  return (res, newNames',newTopnames,newVars)
| `(con_inner| $d:gat_decl ) => do
  let (i,Tnames,T) ← elabGATdecl ctx vars d
  let newVars := λ s =>
    if s=i
    then mkAppM ``V0 #[ ctx , T ]
    else do
      let old ← vars s
      let ID ← mkAppM ``ID #[ctx]
      let p ← mkAppM ``PROJ1 #[ID]
      mkAppM ``SUBST_Tm #[ p , old]
  let res ← mkAppM ``EXTEND #[ctx, T]
  let resNames ← mkAppM ``snoc #[Tnames,mkStrLit i]
  let topsingle ← mkAppM ``stringPure #[mkStrLit i]
  return (res, resNames , topsingle, newVars)
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


partial def elabnamedGAT : Syntax → MetaM Expr
| `(con_outer| ⦃  ⦄ ) => return (.const ``EMPTY [])
| `(con_named| [namedGAT| $s:con_inner ] ) => do
  let (resCon,resList,topList,_) ← elabGATCon_core (.const ``EMPTY []) (λ _ => throwUnsupportedSyntax) s
  -- ListStrToExpr resList
  let filteredList ← mkAppM ``filterNilStr #[resList]
  mkAppM ``mk3 #[resCon,filteredList,topList]
  -- return resList
| _ => throwUnsupportedSyntax


elab g:con_outer : term => elabGATCon g
elab g:con_named : term => elabnamedGAT g
