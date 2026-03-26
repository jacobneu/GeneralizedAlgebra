import GeneralizedAlgebra.typecheck
import Lean

open Lean Elab Meta
open preTy preTm
open Std Format
open Nat

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
syntax "[rawGAT|" con_inner "]" : condata_outer


namespace nouGATmeta

  -- Datatypes
    inductive metaTm : Type where
    | metaGLOB : Nat → metaTm
    | metaLOC : Nat → Nat → metaTm
    | metaAPP : metaTm → metaTm → metaTm
    | metaTRANSP : metaTm → metaTm → metaTm
    open metaTm

    inductive metaArg : Type where
    | metaImpl : String → metaTm → metaTm → metaArg
    | metaExpl : String → metaTm → metaTm → metaArg
    | metaAnon : metaTm → metaTm → metaArg
    open metaArg

    inductive metaTy : Type where
    | metaUU : List metaArg → metaTy
    | metaEl : List metaArg → metaTm → metaTy
    | metaEq : List metaArg → metaTm → metaTm → metaTm → metaTy
    open metaTy


  section decEq
    instance metaTm.decEq : DecidableEq metaTm := fun
    | metaGLOB b1, metaGLOB b2 => match Nat.decEq b1 b2 with
      | isTrue e => isTrue $ by rw [e]
      | isFalse e => isFalse $ by intro c; apply e; injection c
    | metaLOC g1 b1, metaLOC g2 b2 => match (Nat.decEq g1 g2,Nat.decEq b1 b2) with
      | (isTrue e, isTrue e') => isTrue $ by rw [e,e']
      | (isFalse e,_) => isFalse $ by intro c; apply e; injection c
      | (_, isFalse e) => isFalse $ by intro c; apply e; injection c
    | metaAPP f1 x1, metaAPP f2 x2 => match (metaTm.decEq f1 f2, metaTm.decEq x1 x2) with
      | (isTrue e1, isTrue e2) => isTrue $ by rw [e1,e2]
      | (isFalse e, _) => isFalse $ by intro c; apply e; injection c
      | (_,isFalse e) => isFalse $ by intro c; apply e; injection c
    | metaTRANSP p1 x1, metaTRANSP p2 x2 => match (metaTm.decEq p1 p2, metaTm.decEq x1 x2) with
      | (isTrue e1, isTrue e2) => isTrue $ by rw [e1,e2]
      | (isFalse e, _) => isFalse $ by intro c; apply e; injection c
      | (_,isFalse e) => isFalse $ by intro c; apply e; injection c
    | metaAPP _ _, metaLOC _ _ => isFalse metaTm.noConfusion
    | metaTRANSP _ _, metaLOC _ _ => isFalse metaTm.noConfusion
    | metaGLOB _, metaLOC _ _ => isFalse metaTm.noConfusion
    | metaAPP _ _, metaGLOB _ => isFalse metaTm.noConfusion
    | metaTRANSP _ _, metaGLOB _ => isFalse metaTm.noConfusion
    | metaLOC _ _, metaGLOB _ => isFalse metaTm.noConfusion
    | metaLOC _ _, metaAPP _ _ => isFalse metaTm.noConfusion
    | metaGLOB _, metaAPP _ _ => isFalse metaTm.noConfusion
    | metaTRANSP _ _, metaAPP _ _ => isFalse metaTm.noConfusion
    | metaLOC _ _, metaTRANSP _ _ => isFalse metaTm.noConfusion
    | metaGLOB _, metaTRANSP _ _ => isFalse metaTm.noConfusion
    | metaAPP _ _, metaTRANSP _ _ => isFalse metaTm.noConfusion

  end decEq

  section toString
    def metaTm.toString : metaTm → String
    | metaGLOB n => "metaGLOB " ++ Nat.repr n
    | metaLOC g b => "metaLOC (" ++ Nat.repr g ++ "," ++ Nat.repr b ++ ")"
    | metaAPP m1 m2 => "metaAPP (" ++ metaTm.toString m1 ++ ") (" ++ metaTm.toString m2 ++ ")"
    | metaTRANSP m1 m2 => "metaTRANSP (" ++ metaTm.toString m1 ++ ") (" ++ metaTm.toString m2 ++ ")"

    def metaArg.toString
    | metaImpl i _ _ => "Impl(" ++ i ++ ")"
    | metaExpl i _ _ => "Expl("++ i ++ ")"
    | metaAnon _ _ => "Anon"
  end toString

  section extractionComparison
  -- Extraction & comparison
    def extractMetaTm : metaArg → metaTm
    | metaImpl _ m _ => m
    | metaExpl _ m _ => m
    | metaAnon m _ => m

    def extractMetaSort : metaArg → metaTm
    | metaImpl _ _ m => m
    | metaExpl _ _ m => m
    | metaAnon _ m => m

    def argMatch (key : String) : metaArg → Bool
    | metaImpl i _ _ => key=i
    | metaExpl i _ _ => key=i
    | metaAnon _ _ => false
  end extractionComparison

  section weakening
  -- Global Weakening functions
    def metaWkTm
    | metaGLOB b => metaGLOB (succ b)
    | metaLOC g b => metaLOC (succ g) b
    | metaAPP f t => metaAPP (metaWkTm f) (metaWkTm t)
    | metaTRANSP f t => metaTRANSP (metaWkTm f) (metaWkTm t)

    def metaWkArg
    | metaImpl i mt mX => metaImpl i (metaWkTm mt) (metaWkTm mX)
    | metaExpl i mt mX => metaExpl i (metaWkTm mt) (metaWkTm mX)
    | metaAnon mt mX => metaAnon (metaWkTm mt) (metaWkTm mX)

    def metaWkTy
    | metaEl TT t => metaEl (List.map metaWkArg TT) (metaWkTm t)
    | metaEq TT X s t => metaEq (List.map metaWkArg TT) (metaWkTm X) (metaWkTm s) (metaWkTm t)
    | metaUU TT => metaUU (List.map metaWkArg TT)

  -- Local weakening functions
    def localWkTm
    | metaGLOB b => metaGLOB b
    | metaLOC g b => metaLOC g (succ b)
    | metaAPP f t => metaAPP (localWkTm f) (localWkTm t)
    | metaTRANSP f t => metaTRANSP (localWkTm f) (localWkTm t)

    def localWkSortOnly
    | metaImpl i mt mX => metaImpl i mt (localWkTm mX)
    | metaExpl i mt mX => metaExpl i mt (localWkTm mX)
    | metaAnon mt mX => metaAnon mt (localWkTm mX)

    def localWkArg
    | metaImpl i mt mX => metaImpl i (localWkTm mt) (localWkTm mX)
    | metaExpl i mt mX => metaExpl i (localWkTm mt) (localWkTm mX)
    | metaAnon mt mX => metaAnon (localWkTm mt) (localWkTm mX)

  end weakening

  section substitution
  -- Substitution functions
    def metaSubstTm (s t q : metaTm) : metaTm := if q = s then t else
    match q with
    | metaAPP f x => metaAPP (metaSubstTm s t f) (metaSubstTm s t x)
    | metaTRANSP p x => metaTRANSP (metaSubstTm s t p) (metaSubstTm s t x)
    | z => z

    def metaSubstArg (s t : metaTm) : metaArg → metaArg
    | metaImpl i mt mX => metaImpl i (metaSubstTm s t mt) (metaSubstTm s t mX)
    | metaExpl i mt mX => metaExpl i (metaSubstTm s t mt) (metaSubstTm s t mX)
    | metaAnon mt mX => metaAnon (metaSubstTm s t mt) (metaSubstTm s t mX)

  end substitution

  section literals
  -- Make literal for rawGAT
    def mkMetaTmLit : metaTm → Expr -- :: metaTm
    | metaLOC g b => mkAppN (.const ``metaLOC []) #[mkNatLit g,mkNatLit b]
    | metaGLOB b => .app (.const ``metaGLOB []) (mkNatLit b)
    | metaAPP m1 m2 => mkApp2 (.const ``metaAPP []) (mkMetaTmLit m1) (mkMetaTmLit m2)
    | metaTRANSP m1 m2 => mkApp2 (.const ``metaTRANSP []) (mkMetaTmLit m1) (mkMetaTmLit m2)

    def mkMetaArgLit : metaArg → MetaM Expr -- :: String × metaTm
    | metaImpl i mt mX => mkAppM `Prod.mk #[mkStrLit $ i ++ "=" ++ mt.toString,mkMetaTmLit mX]
    | metaExpl i mt mX => mkAppM `Prod.mk #[mkStrLit $ i ++ "=" ++ mt.toString,mkMetaTmLit mX]
    | metaAnon mt mX => mkAppM `Prod.mk #[mkStrLit $ "_=" ++ mt.toString,mkMetaTmLit mX]

    def metaOut := String × List (String × metaTm)
    def metaOut' := String × metaTm

    def mkMetaTyLit : metaTy → MetaM Expr -- :: String × List (String × metaTm)
    | metaUU TT => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaOut' [])
        mkAppM ``Prod.mk #[mkStrLit "UU",mTT]
    | metaEq TT X s t => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaOut' [])
        mkAppM ``Prod.mk #[mkStrLit $ "Eq _(" ++ metaTm.toString X ++")(" ++ metaTm.toString s ++ ") (" ++ metaTm.toString t ++ ")",mTT]
    | metaEl TT t => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaOut' [])
        mkAppM ``Prod.mk #[mkStrLit $ "El (" ++ metaTm.toString t ++ ")",mTT]

  -- Make literal for GATdata
    def mkMetaArgLit' : metaArg → Expr -- :: Option String
    | metaImpl i _ _ => mkApp (.app (.const ``some [Level.zero]) (.const ``String [])) $ mkStrLit i
    | metaExpl i _ _ => mkApp (.app (.const ``some [Level.zero]) (.const ``String [])) $ mkStrLit i
    | metaAnon _ _ => .app (.const ``none [Level.zero]) (.const ``String [])

    def StringOpt : Type := Option String
    def StringOptList : Type := List StringOpt

    def mkMetaTyLit' : metaTy → MetaM Expr -- :: List (Option String)
    | metaUU TT => mkListLit (.const ``StringOpt []) (List.map mkMetaArgLit' (List.reverse TT))
    | metaEq TT _ _ _ => mkListLit (.const ``StringOpt []) (List.map mkMetaArgLit' (List.reverse TT))
    | metaEl TT _ => mkListLit (.const ``StringOpt []) (List.map mkMetaArgLit' (List.reverse TT))
  end literals

end nouGATmeta

namespace elabState

  open nouGATmeta
  open metaTy metaArg

  -- Variable structures
    structure varStruct where
      (lkup : String → String → MetaM Nat)
      (topnames : List String)
      (telescopes : List metaTy)

    def varExtend (VV : varStruct) (key : String) (metResT : metaTy): varStruct :=
      ⟨
        λ s mess =>
            if s=key
            then return 0
            else succ <$> VV.lkup s (mess ++ "tried1 \"" ++ key ++ "\" vs. \"" ++  s ++ "\"; "),
        key::VV.topnames,
        metResT::List.map metaWkTy VV.telescopes
      ⟩

    def varEmpty : varStruct :=
      ⟨ λ s mess => throwError ("Unknown var: " ++ s ++ ". Info dump:" ++ mess), [], [] ⟩

  -- Variables
    inductive varKind : Type where
    | LOC : Nat → varKind
    | GLOB : Nat → varKind
    open varKind

    def wkVar : varKind → varKind
    | LOC b => LOC $ succ b
    | GLOB b => GLOB b

    -- TODO: reimplement using LL[n]?
    partial def getN {A : Type} (message : String) : List A → Nat → MetaM A
    | [], _ => throwError message
    | x::_, 0 => return x
    | _::xs, succ n => getN message xs n


  -- Lookup
    def varTelLkup : List metaArg → String → String → StateT varStruct MetaM (varKind × metaTy)
    | [], key, message => do
        let VV ← get
        let b ← VV.lkup key message
        let tel ← getN "Issue accessing arity" VV.telescopes b
        return (GLOB b,metaWkTy tel)
    | a::rest, key, message =>
      if argMatch key a
      then return (LOC 0,metaEl [] $ extractMetaSort a)
      else  (λ (v,mt) => (wkVar v,mt)) <$> varTelLkup rest key (message ++ "tried2 \"" ++ a.toString ++ "\"; ")

end elabState

namespace elaborator

    open nouGATmeta
    open elabState
    open metaTm metaArg metaTy varKind
    open Nat

  -- The rawGAT type
    structure rawGAT where
      (con : preCon)
      (topnames : List String)
      (telescopes : List metaOut)

  -- Failure-prone helper functions
  section failureHelpers

    -- TODO: reimplement using List.getLast? and List.dropLast
    def initLast {A : Type} : List A → MetaM (List A × A)
    | [] => throwError "Shouldn't happen"
    | [x] => return ([],x)
    | (x::xs) => (λ (res,f) => (x::res,f)) <$> initLast xs

    def metaTyMatch : metaArg → metaTm → metaTy → MetaM metaTy
    | metaImpl _ _ m1, m2, res => if m1 = m2 then return res else throwError ("Error: expected " ++ metaTm.toString m1 ++ ", got " ++ metaTm.toString m2)
    | metaExpl _ _ m1, m2, res => if m1 = m2 then return res else throwError ("Error: expected " ++ metaTm.toString m1 ++ ", got " ++ metaTm.toString m2)
    | metaAnon _ m1, m2, res => if m1 = m2 then return res else throwError ("Error: expected " ++ metaTm.toString m1 ++ ", got " ++ metaTm.toString m2)

    def locSubstTy (t : metaTm) : metaTy → MetaM (metaTy × metaArg)
    | metaEl [] _ => throwError "Tried to perform dummy substitution"
    | metaEq [] _ _ _ => throwError "Tried to perform dummy substitution"
    | metaUU [] => throwError "Tried to perform dummy substitution"
    | metaUU args => do
        let (rest,arg) ← initLast args
        let s := extractMetaTm arg
        return (metaUU (List.map (metaSubstArg s t) rest),arg)
    | metaEl args finalT => do
        let (rest,arg) ← initLast args
        let s := extractMetaTm arg
        return (metaEl (List.map (metaSubstArg s t) rest) (metaSubstTm s t finalT),arg)
    | metaEq args finalT ms mt => do
        let (rest,arg) ← initLast args
        let s := extractMetaTm arg
        return (metaEq (List.map (metaSubstArg s t) rest) (metaSubstTm s t finalT) (metaSubstTm s t ms) (metaSubstTm s t mt),arg)

    partial def metaTyApp : metaTy → metaTm →  metaTy → MetaM metaTy
    | _, _, metaUU _ => throwError ("Error: applied function to sort argument")
    | _, _, metaEq _ _ _ _ => throwError ("Error: applied function to equation argument")
    | _, _, metaEl (_::_) _ => throwError ("Error: applied function to open argument")
    | metaUU [], _,_ => throwError "Too many arguments"
    | metaEq [] _ _ _, _,_ => throwError "Too many arguments"
    | metaEl [] _, _,_ => throwError "Too many arguments"
    | metaUU args, s, metaEl [] y => do
        let (finalT',x) ← locSubstTy s (metaUU args)
        metaTyMatch x y finalT'
    | metaEl args finalT, s, metaEl [] y => do
        let (finalT',x) ← locSubstTy s (metaEl args finalT)
        metaTyMatch x y finalT'
    | metaEq args finalT ms mt , s, metaEl [] y => do
        let (finalT',x) ← locSubstTy s (metaEq args finalT ms mt)
        metaTyMatch x y finalT'


    partial def failIfBadTransp (tm1 tm2 message : String) : metaTy → metaTy → MetaM metaTy
    | metaEq [] _ ms mt, metaEl [] mq => return (metaEl [] $ metaSubstTm ms mt mq)
    | metaEq (_::_) _ _ _, metaEl _ _ => throwError ("Error: Bad transport: " ++ tm1 ++ " has open variables. Did you forget an argument?." ++ message)
    | metaEq [] _ _ _, metaEl _ _ => throwError ("Error: Bad transport: " ++ tm2 ++ " has open variables. Did you forget an argument?." ++ message)
    | metaEl _ _ , _ => throwError ("Error: Bad transport: " ++ tm1 ++ " is an element, not an equality." ++ message)
    | metaUU _ , _ => throwError ("Error: Bad transport: " ++ tm1 ++ " is a sort, not an equality." ++ message)
    | _, metaEq _ _ _ _  => throwError ("Error: Bad transport: " ++ tm2 ++ " is an equality, not an element." ++ message)
    | _, metaUU _ => throwError ("Error: Bad transport: " ++ tm2 ++ " is a sort, not an element." ++ message)

    partial def failIfNotU (tmName : String) : metaTy → MetaM Unit
    | metaUU [] => return ()
    | metaUU args => throwError ("Error: " ++ tmName ++ " contains open variables. Did you forget an argument?. [" ++ (String.intercalate ",\n" $ (List.map (λ a => (extractMetaTm a).toString ++ ":" ++ (extractMetaSort a).toString) args)))
    | metaEq args mX ms mt => throwError ("Error: " ++ tmName ++ "is an equality (" ++ ms.toString ++ " ≡ " ++ mt.toString ++ " in " ++ mX.toString ++", with " ++ Nat.repr (List.length args) ++ " fv's), not a sort. [" ++ (String.intercalate ",\n" $ (List.map (λ a => (extractMetaTm a).toString ++ ":" ++ (extractMetaSort a).toString) args)))
    | metaEl args mt => throwError ("Error: " ++ tmName ++ "is an element (" ++ mt.toString ++ "), not a sort. [" ++ (String.intercalate ",\n" $ (List.map (λ a => (extractMetaTm a).toString ++ ":" ++ (extractMetaSort a).toString) args)))

    partial def failIfBadEq (tm1 tm2 : String) : metaTy → metaTy → MetaM metaTm
    | metaEl [] mt1, metaEl [] mt2 => if mt1 = mt2 then return mt1 else throwError ("Error: Bad eq: term " ++ tm1 ++ " is an element of " ++ metaTm.toString mt1 ++ " but " ++ tm2 ++ " is an element of " ++ metaTm.toString mt2)
    | metaEl _ _, metaEl [] _ => throwError ("Error: Bad eq: term " ++ tm1 ++ " has open variables")
    | metaEl [] _, metaEl _ _ => throwError ("Error: Bad eq: term" ++ tm2 ++ " has open variables")
    | metaEl _ _, metaEl _ _ => throwError ("Error: Bad eq: terms " ++ tm1 ++ " and " ++ tm2 ++ " have open variables")
    | metaUU _, _ => throwError ("Error: Bad eq: term " ++ tm1 ++ " is a sort")
    | metaEq _ mX ms mt, _ => throwError ("Error: Bad eq: term " ++ tm1 ++ " is an equality (" ++ ms.toString ++ " ≡ " ++ mt.toString ++ " in " ++ mX.toString ++")")
    | _, metaUU _ => throwError ("Error: Bad eq: term " ++ tm2 ++ " is a sort")
    | _, metaEq _ mX ms mt => throwError ("Error: Bad eq: term " ++ tm2 ++ " is an equality (" ++ ms.toString ++ " ≡ " ++ mt.toString ++ " in " ++ mX.toString ++")")

  end failureHelpers

  section mainFunctions

    instance  : Inhabited (Syntax → StateT varStruct MetaM (Expr × metaTm × metaTy)) where
      default _ := pure (.const ``true [],metaGLOB 0,metaUU [])

    partial def elabGATTm (TT : List metaArg) : Syntax → StateT varStruct MetaM (Expr × metaTm × metaTy)
    | `(gat_tm| ( $g:gat_tm ) ) => elabGATTm TT g
    | `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
          let (t1,mt1,mA1) ← elabGATTm TT g1
          let (t2,mt2,mA2) ← elabGATTm TT g2
          let mRes ← metaTyApp mA1 mt2 mA2
          let resT ← mkAppM ``preAPP #[t1,t2]
          return (resT, metaAPP mt1 mt2,mRes)
    | `(gat_tm| $i:ident ) => do
          let (bv,m) ← varTelLkup TT i.getId.toString ("Lookup \"" ++ i.getId.toString ++ "\"; ")
          let (b,mb) := match bv with
            | LOC b => (b,metaLOC 0 b)
            | GLOB b => (b + List.length TT,metaGLOB (succ b))
          let res ← mkAppM ``preVAR #[mkNatLit b]
          return (res,mb,m)
    | `(gat_tm| $g1 #⟨ $g2 ⟩ ) => do
          let (t1,mt1,mX1) ← elabGATTm TT g1
          let (t2,mt2,mX2) ← elabGATTm TT g2
          let mresT ← failIfBadTransp (mt2.toString) (mt1.toString) (String.intercalate "," $ List.map metaTm.toString (List.map extractMetaTm TT)) mX2 mX1
          let resT ← mkAppM ``preTRANSP #[t2,t1]
          return (resT,metaTRANSP mt2 mt1,mresT)
    | _ => throwError "TmFail"

    partial def elabGATArg (TT : List metaArg) : Syntax → StateT varStruct MetaM (Expr × metaArg)
    | `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
      let (t,mt,mX) ← elabGATTm TT g
      failIfNotU (metaTm.toString mt) mX
      return (t,metaExpl i.getId.toString (metaLOC 0 0) mt)
    | `(gat_arg| ( _ : $g:gat_tm ) ) => do
      let (t,mt,mX) ← elabGATTm TT g
      failIfNotU (metaTm.toString mt) mX
      return (t, metaAnon (metaLOC 0 0) mt)
    | `(gat_arg| $g:gat_tm ) => do
      let (t,mt,mX) ← elabGATTm TT g
      failIfNotU (metaTm.toString mt) mX
      return (t, metaAnon (metaLOC 0 0) mt)
    | _ => throwError "ArgFail"

    instance  : Inhabited (Syntax → StateT varStruct MetaM (Expr × metaTy)) where
      default _ := pure (.const ``true [],metaUU [])

    partial def elabGATTy (TT : List metaArg) : Syntax → StateT varStruct MetaM (Expr × metaTy)
    | `(gat_ty| U ) => return (.const ``preUU [],metaUU TT)
    | `(gat_ty| $x:gat_tm ) => do
        let (t,mt,mX) ← elabGATTm TT x
        failIfNotU (metaTm.toString mt) mX
        let T ← mkAppM ``preEL #[t]
        return (T,metaEl TT mt)
    | `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
        let (domain,argT) ← elabGATArg TT T
        let (codomain,finalT) ← elabGATTy ((localWkSortOnly argT)::List.map localWkArg TT) T'
        let result ← mkAppM  ``prePI #[domain,codomain]
        return (result,finalT)
    | `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
        let (tt1,mt1,mX1) ← elabGATTm TT t1
        let (tt2,mt2,mX2) ← elabGATTm TT t2
        let mX ← failIfBadEq (metaTm.toString mt1) (metaTm.toString mt2) mX1 mX2
        let T ← mkAppM ``preEQ #[tt1,tt2]
        return (T,metaEq TT mX mt1 mt2)
    | _ => throwError "TyFail"

    -- returns (the preTy, the topname, the telescope)
    partial def elabGATdecl : Syntax → StateT varStruct MetaM (Expr × String × metaTy)
    | `(gat_decl| $i:ident : $g:gat_ty ) => do
        let (T,finalT) ← elabGATTy [] g
        return (T,i.getId.toString,finalT)
    | _ => throwError "declFail"


    partial def elabGATCon_core : Syntax → StateT varStruct MetaM Expr
    | `(con_inner| $rest:con_inner , $d:gat_decl ) => do
        let restCon ← elabGATCon_core rest
        let (T,i,finalT) ← elabGATdecl d
        let newCtx ← mkAppM ``preEXTEND #[restCon, T]
        let restVars ← get
        set $ varExtend restVars i finalT
        return newCtx
    | `(con_inner| $d:gat_decl ) => do
        let (T,i,finalT) ← elabGATdecl d
        let newCtx ← mkAppM ``preEXTEND #[.const ``preEMPTY [],T]
        let restVars ← get
        set $ varExtend restVars i finalT
        return newCtx
    | _ => throwError "Con_coreFail"



    partial def elabGATConData : Syntax → MetaM Expr
    | `(condata_outer| [GATdata| ] ) => do
        let emptyStrList ← mkListLit (.const ``String []) []
        let emptyLArgList ← mkListLit (.const ``metaArg []) []
        let res ← mkAppM ``GATdata.mk  #[.const ``preEMPTY [],emptyStrList,emptyLArgList]
        return res
    | `(condata_outer| [rawGAT| $s:con_inner ] ) => do
        let (resCon,VV) ← StateT.run (elabGATCon_core s) varEmpty
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit VV.topnames)
        let telescopes ← List.mapM mkMetaTyLit VV.telescopes >>= mkListLit (.const ``metaOut [])
        let res ← mkAppM ``rawGAT.mk #[resCon,topList,telescopes]
        return res
    | `(condata_outer| [GATdata| $s:con_inner ] ) => do
        let (resCon,VV) ← StateT.run (elabGATCon_core s) varEmpty
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit (List.reverse VV.topnames))
        let telescopes ← List.mapM mkMetaTyLit' (List.reverse VV.telescopes) >>= mkListLit (.const ``StringOptList [])
        let res ← mkAppM ``GATdata.mk #[resCon,topList,telescopes]
        return res
    | _ => throwError "ConFail"

  end mainFunctions

elab g:condata_outer : term => elabGATConData g
