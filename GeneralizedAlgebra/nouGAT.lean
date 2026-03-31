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

    inductive metaArgMarker : Type where
    | mkImpl : String → metaTm → metaArgMarker
    | mkExpl : String → metaTm → metaArgMarker
    | mkAnon : metaTm → metaArgMarker
    open metaArgMarker

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

    def extractTel : metaTy → List metaArg
    | metaUU l => l
    | metaEq l _ _ _=> l
    | metaEl l _ => l

    def extractName : metaArg → String
    | metaImpl i _ _ => i
    | metaExpl i _ _ => i
    | metaAnon _ _ => "_"

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

    def metaWkSortOnly
    | metaImpl i mt mX => metaImpl i mt (metaWkTm mX)
    | metaExpl i mt mX => metaExpl i mt (metaWkTm mX)
    | metaAnon mt mX => metaAnon mt (metaWkTm mX)

    def metaWkTy
    | metaEl TT t => metaEl (List.map metaWkArg TT) (metaWkTm t)
    | metaEq TT X s t => metaEq (List.map metaWkArg TT) (metaWkTm X) (metaWkTm s) (metaWkTm t)
    | metaUU TT => metaUU (List.map metaWkArg TT)

    def metaWkTySortOnly
    | metaEl TT t => metaEl (List.map metaWkSortOnly TT) t
    | metaEq TT X s t => metaEq (List.map metaWkSortOnly TT) (metaWkTm X) s t
    | metaUU TT => metaUU (List.map metaWkSortOnly TT)

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
  open metaTm metaTy metaArg metaArgMarker

    structure st where
      (topnames : List String)
      (telescopes : List metaTy)
      (currentName : Option String)
      (currentTel : List metaArg)
      (rawMode : Bool)

    def stEmpty (raw : Bool) : st := ⟨[],[],none,[],raw⟩

  section toString

    def metaTmFormat (current : st) : metaTm → String
    | metaGLOB n => let gIndex := current.topnames.length; match current.topnames[gIndex - n - 1]? with
      | some s => s ++ (if current.rawMode then "[" ++ Nat.repr n ++ "]" else "")
      | none => "???" ++ (if current.rawMode then "[" ++ Nat.repr n ++ "]" else "")
    | metaLOC g b => let gIndex := current.topnames.length;
      if g = gIndex then match current.currentTel[b]? with
        | some a => (extractName a) ++ (if current.rawMode then "[" ++ Nat.repr g ++ ","++ Nat.repr b ++ "]" else "")
        | none => "???" ++ (if current.rawMode then "[" ++ Nat.repr g ++ ","++ Nat.repr b ++ "]" else "")
      else
      match current.telescopes[gIndex - g - 1]? with
      | some mX => match (extractTel mX)[b]? with
        | some a => (extractName a) ++ (if current.rawMode then "[" ++ Nat.repr g ++ ","++ Nat.repr b ++ "]" else "")
        | none => "???" ++ (if current.rawMode then "[" ++ Nat.repr g ++ ","++ Nat.repr b ++ "]" else "")
      | none => "???" ++ (if current.rawMode then "[" ++ Nat.repr g ++ ","++ Nat.repr b ++ "]" else "")
    | metaAPP m1 m2 => mkParen (metaTmFormat current m1) ++ " " ++ mkParen (metaTmFormat current m2)
    | metaTRANSP m1 m2 =>  mkParen (metaTmFormat current m2) ++ " #⟨" ++ metaTm.toString m1 ++ "⟩"

    def metaArgFormat (current : st) : metaArg → String
    | metaImpl i mt mX => "{" ++ i ++ (if current.rawMode then "=" ++ mt.toString else "") ++ " : " ++ metaTmFormat current mX ++ "}"
    | metaExpl i mt mX => "(" ++ i ++ (if current.rawMode then "=" ++ mt.toString else "") ++ " : " ++ metaTmFormat current mX ++ ")"
    | metaAnon mt mX => "_" ++ (if current.rawMode then "=" ++ mt.toString else "") ++ " : " ++ metaTmFormat current mX

    def formatList (ind : Nat) : List Format → Format
    | [] => ""
    | [x] => (nest ind <| (align true) ++ x)
    | (x::y::zs) => (nest ind <| (align true) ++ x) ++ formatList ind (y::zs)

    def metaTyFormatDisp (current : st) (ind : Nat) (theTy : metaTy) (outername := "_") : Format := match theTy with
    | metaEl TT mX => formatList ind ((List.map (text ∘ metaArgFormat current) (List.reverse TT)) ++ [text " ⊢ ",outername ++ " : " ++ (metaTmFormat current mX)])
    | metaUU TT => formatList ind ((List.map (text ∘ metaArgFormat current) (List.reverse TT)) ++ [text " ⊢ ",outername ++ " : U"])
    | metaEq TT _ ms mt => formatList ind ((List.map (text ∘ metaArgFormat current) (List.reverse TT)) ++ [text " ⊢ ",outername ++ " : " ++ (metaTmFormat current ms) ++ " = " ++ (metaTmFormat current mt)])

    def metaTyFormat (current : st) (theTy : metaTy) (outername := "_") : Format := match theTy with
    | metaEl TT mX => (String.intercalate ", " (List.map (metaArgFormat current) (List.reverse TT))) ++ " ⊢ " ++ outername ++ " : " ++ (metaTmFormat current mX)
    | metaUU TT => (String.intercalate ", " (List.map (metaArgFormat current) (List.reverse TT))) ++ " ⊢ " ++ outername ++ " : U"
    | metaEq TT _ ms mt => (String.intercalate ", " (List.map (metaArgFormat current) (List.reverse TT))) ++ " ⊢ " ++ outername ++ " : " ++ (metaTmFormat current ms) ++ " = " ++ (metaTmFormat current mt)

    def previousFormat (current : st) : String × metaTy → Format
    | (s,T) => metaTyFormat current T s

  end toString

    def findIdxElem {α} (p : α → Bool) (l : List α) : Option (Nat × α) := do
      let elem ← List.find? p l
      let idx ← List.findIdx? p l
      return (idx,elem)

    def varTelLkup_core (key : String) : StateT st MetaM (Option (metaTm × metaTy × Nat)) := do
        let current ← get
        let gIndex := current.topnames.length
        match findIdxElem (argMatch key) current.currentTel with
        | some (idx,a) => return (metaLOC gIndex idx,metaEl [] $ extractMetaSort a,idx)
        | none => match findIdxElem (λ (s,_) => s == key) (List.zip current.topnames current.telescopes) with
          | some (idx,_,T) => return (metaGLOB (gIndex - idx - 1),T,idx + current.currentTel.length)
          | none => return none

  section failure
    inductive errorCode : Type where
    | errOther : errorCode
    | errOption : errorCode
    | errUnknownVar : String → errorCode
    | errType : metaTm → metaTm → errorCode
    | errType2 : String → metaTm → String → metaTm → errorCode
    | errOpen : metaTm → metaTy → errorCode
    | errKind : metaTm → metaTy → String → String → errorCode
    | errTooManyArgs : metaTm → metaTy → errorCode
    open errorCode

    def errorCode.format (suberror : String) : errorCode → StateT st MetaM Format
    | errOther => return text suberror
    | errOption => return text $ "Failure when " ++ suberror ++ ": got none"
    | errUnknownVar s => return text $ ": Unknown variable: `" ++ s ++ "`"
    | errType m1 m2 => do
        let current ← get
        let s1 := metaTmFormat current m1
        let s2 := metaTmFormat current m2
        return text $ "expected " ++ s1 ++ ", got " ++ s2
    | errType2 s1 m1 s2 m2 => do
        let current ← get
        return (text $ suberror ++ ": Type mismatch: ")
          ++ (nest 3 <| (align true) ++ s1 ++ " is element of ")
          ++ (nest 5 <| (align true) ++ metaTmFormat current m1 ++ ", ")
          ++ (nest 3 <| (align true) ++ s2 ++ " is element of ")
          ++ (nest 5 <| (align true) ++ metaTmFormat current m2 ++ ".")
    | errOpen mt mX => do
        let current ← get
        let ts := metaTmFormat current mt
        let Xs := metaTyFormatDisp current 4 mX ts
        return (text $ suberror ++ ": Open variable: ") ++ Xs
    | errKind mt mX given exp => do
        let current ← get
        let ts := metaTmFormat current mt
        let Xs := metaTyFormatDisp current 4 mX ts
        return ((text $ suberror ++ ": ") ++ ts ++ (text $ " is " ++ given ++ " not " ++ exp)) ++ Xs
    | errTooManyArgs mf mF => do
        let current ← get
        let fs := metaTmFormat current mf
        let Fs := metaTyFormatDisp current 4 mF fs
        return (text $ suberror ++ ": Too many arguments supplied to") ++ fs ++ Fs





    def elabFail {α : Type} (suberror : String) (err : errorCode) : StateT st MetaM α := do
        let current ← get
        let errFmt ← err.format suberror
        throwError (nest 0 <| (align true) ++ "Error: " ++ errFmt)
           ++ (match current.currentName with | some s => (nest 2 <| (align true) ++ "while laborating constructor: " ++ s) | _ => "")
           ++ (match current.currentTel with | [] => "" | l => (nest 2 <| (align true) ++ "telescope: " ++ formatList 4 (List.reverse $ List.map (λ a => "- " ++ metaArgFormat current a) l)))
           ++ (nest 2 <| (align true) ++ "previous: " ++ formatList 4 (List.map (previousFormat current) $ List.reverse $ List.zip current.topnames current.telescopes))

    def optFail {α : Type} (message : String) : Option α → StateT st MetaM α
    | some x => return x
    | none => elabFail message errOption


  end failure


    def extendMain (finalT : metaTy) : StateT st MetaM Unit := do
      let current ← get
      let theName ← optFail "getting name for extension" current.currentName
      set (st.mk (theName::current.topnames) (finalT::current.telescopes) none [] current.rawMode)

    def extendTel (newArgMark : metaArgMarker) : StateT st MetaM Unit := do
      let current ← get
      let gIndex := current.topnames.length
      let newArg := match newArgMark with
        | mkImpl i mX => metaImpl i (metaLOC gIndex 0) (localWkTm mX)
        | mkExpl i mX => metaExpl i (metaLOC gIndex 0) (localWkTm mX)
        | mkAnon mX => metaAnon (metaLOC gIndex 0) (localWkTm mX)
      set (st.mk current.topnames current.telescopes current.currentName (newArg::List.map localWkArg current.currentTel) current.rawMode)

    def setCurrentName (theName : String) : StateT st MetaM Unit := do
      let current ← get
      set (st.mk current.topnames current.telescopes (some theName) current.currentTel current.rawMode)

    def getCurrentTel : StateT st MetaM (List metaArg) := do
      let current ← get
      return current.currentTel

    def varTelLkup (key : String) : StateT st MetaM (metaTm × metaTy × Nat) := do
        let resO ← varTelLkup_core key
        match resO with
          | some z => return z
          | none => elabFail "" (errorCode.errUnknownVar key)

end elabState

namespace elaborator

    open nouGATmeta
    open elabState
    open metaTm metaArg metaArgMarker metaTy
    open Nat

  -- The rawGAT type
    structure rawGAT where
      (con : preCon)
      (topnames : List String)
      (telescopes : List metaOut)

  -- Failure-prone helper functions
  section failureHelpers

    def initLast {A : Type} (l : List A) : Option (List A × A) := do
        let last ← List.getLast? l
        let init := List.dropLast l
        return (init,last)

    def metaTyMatch (suberror : String): metaArg → metaTm → metaTy → StateT st MetaM metaTy
    | metaImpl _ _ m1, m2, res => if m1 = m2 then return res else elabFail suberror (errorCode.errType m1 m2)
    | metaExpl _ _ m1, m2, res => if m1 = m2 then return res else elabFail suberror (errorCode.errType m1 m2)
    | metaAnon _ m1, m2, res => if m1 = m2 then return res else elabFail suberror (errorCode.errType m1 m2)

    def locSubstTy (t : metaTm) : metaTy → StateT st MetaM (metaTy × metaArg)
    | metaUU args => do
        let (rest,arg) ← optFail "Tried to perform dummy substitution" (initLast args)
        let s := extractMetaTm arg
        return (metaUU (List.map (metaSubstArg s t) rest),arg)
    | metaEl args finalT => do
        let (rest,arg) ← optFail "Tried to perform dummy substitution" (initLast args)
        let s := extractMetaTm arg
        return (metaEl (List.map (metaSubstArg s t) rest) (metaSubstTm s t finalT),arg)
    | metaEq args finalT ms mt => do
        let (rest,arg) ← optFail "Tried to perform dummy substitution" (initLast args)
        let s := extractMetaTm arg
        return (metaEq (List.map (metaSubstArg s t) rest) (metaSubstTm s t finalT) (metaSubstTm s t ms) (metaSubstTm s t mt),arg)

    partial def metaTyApp (fnTm : metaTm) (fnTy : metaTy) (argTm : metaTm) (argTy : metaTy) : StateT st MetaM metaTy := match (fnTy,argTy) with
    | (_, metaUU _) => elabFail "Bad argument" (errorCode.errKind argTm argTy "a sort" "an element")
    | (_,  metaEq _ _ _ _) => elabFail "Bad argument" (errorCode.errKind argTm argTy "an equation" "an element")
    | (_,  metaEl (_::_) _) => elabFail "Bad argument" (errorCode.errOpen argTm argTy)
    | (metaUU [], _) => elabFail "Bad function" (errorCode.errTooManyArgs fnTm fnTy)
    | (metaEq [] _ _ _, _) => elabFail "Bad function" (errorCode.errTooManyArgs fnTm fnTy)
    | (metaEl [] _, _) => elabFail "Bad function" (errorCode.errTooManyArgs fnTm fnTy)
    | (metaUU args, metaEl [] y) => do
        let (finalT',x) ← locSubstTy argTm (metaUU args)
        metaTyMatch "Bad application" x y finalT'
    | (metaEl args finalT, metaEl [] y) => do
        let (finalT',x) ← locSubstTy argTm (metaEl args finalT)
        metaTyMatch "Bad application" x y finalT'
    | (metaEq args finalT ms mt ,  metaEl [] y) => do
        let (finalT',x) ← locSubstTy argTm (metaEq args finalT ms mt)
        metaTyMatch "Bad application" x y finalT'


    partial def failIfBadTransp (tm1 tm2 : metaTm) (T1 T2 : metaTy) : StateT st MetaM metaTy := match (T1,T2) with
    | (metaEq [] _ ms mt, metaEl [] mq) => return (metaEl [] $ metaSubstTm ms mt mq)
    | (metaEq (_::_) _ _ _, metaEl _ _) => elabFail "Bad transport" (errorCode.errOpen tm1 T1)
    | (metaEq [] _ _ _, metaEl _ _) => elabFail "Bad transport" (errorCode.errOpen tm2 T2)
    | (metaEl _ _ , _) => elabFail "Bad transport" (errorCode.errKind tm1 T1 "an element" "an equality")
    | (metaUU _ , _) =>  elabFail "Bad transport" (errorCode.errKind tm1 T1 "a sort" "an equality")
    | (_, metaEq _ _ _ _)  => elabFail "Bad transport" (errorCode.errKind tm2 T2 "an equality" "an element")
    | (_, metaUU _) => elabFail "Bad transport" (errorCode.errKind tm2 T2 "a sort" "an element")

    partial def failIfNotU (suberror : String) (theTm : metaTm) (theTy : metaTy) : StateT st MetaM Unit := match theTy with
    | metaUU [] => return ()
    | metaUU _ => elabFail suberror (errorCode.errOpen theTm theTy)
    | metaEq _ _ _ _ => elabFail suberror (errorCode.errKind theTm theTy "an equality" "a sort")
    | metaEl _ _  => elabFail suberror (errorCode.errKind theTm theTy "an element" "a sort")

    partial def failIfBadEq (tm1 tm2 : metaTm) (T1 T2 : metaTy) : StateT st MetaM metaTm := match (T1,T2) with
    | (metaEl [] mX1, metaEl [] mX2) => if mX1 = mX2 then return mX1 else
    elabFail "Bad eq" (errorCode.errType2 "LHS" mX1 "RHS" mX2)
    | (metaEl (_::_) _, metaEl _ _) => elabFail "Bad eq" (errorCode.errOpen tm1 T1)
    | (metaEl _ _, metaEl _ _) => elabFail "Bad eq" (errorCode.errOpen tm2 T2)
    | (metaUU _, _) => elabFail "Bad eq" (errorCode.errKind tm1 T1 "a sort" "an element")
    | (metaEq _ _ _ _, _) => elabFail "Bad eq" (errorCode.errKind tm1 T1 "an equality" "an element")
    | (_, metaUU _) => elabFail "Bad eq" (errorCode.errKind tm2 T2 "a sort" "an element")
    | (_, metaEq _ _ _ _) => elabFail "Bad eq" (errorCode.errKind tm2 T2 "an equality" "an element")

  end failureHelpers

  section mainFunctions

    instance  : Inhabited (Syntax → StateT st MetaM (Expr × metaTm × metaTy)) where
      default _ := pure (.const ``true [],metaGLOB 0,metaUU [])

    partial def elabGATTm : Syntax → StateT st MetaM (Expr × metaTm × metaTy)
    | `(gat_tm| ( $g:gat_tm ) ) => elabGATTm g
    | `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
          let (t1,mt1,mA1) ← elabGATTm g1
          let (t2,mt2,mA2) ← elabGATTm g2
          let mRes ← metaTyApp mt1 mA1 mt2 mA2
          let resT ← mkAppM ``preAPP #[t1,t2]
          return (resT, metaAPP mt1 mt2,mRes)
    | `(gat_tm| $i:ident ) => do
          let (mb,m,b) ← varTelLkup i.getId.toString
          let res ← mkAppM ``preVAR #[mkNatLit b]
          return (res,mb,m)
    | `(gat_tm| $g1 #⟨ $g2 ⟩ ) => do
          let (t1,mt1,mX1) ← elabGATTm g1
          let (t2,mt2,mX2) ← elabGATTm g2
          let mresT ← failIfBadTransp mt2 mt1 mX2 mX1
          let resT ← mkAppM ``preTRANSP #[t2,t1]
          return (resT,metaTRANSP mt2 mt1,mresT)
    | _ => throwError "TmFail"

    partial def elabGATArg : Syntax → StateT st MetaM Expr
    | `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
      let (t,mt,mX) ← elabGATTm g
      failIfNotU "Failed to create argument" mt mX
      extendTel (mkExpl i.getId.toString mt)
      return t
    | `(gat_arg| ( _ : $g:gat_tm ) ) => do
      let (t,mt,mX) ← elabGATTm g
      failIfNotU "Failed to create argument" mt mX
      extendTel (mkAnon mt)
      return t
    | `(gat_arg| $g:gat_tm ) => do
      let (t,mt,mX) ← elabGATTm g
      failIfNotU "Failed to create argument" mt mX
      extendTel (mkAnon mt)
      return t
    | _ => throwError "ArgFail"

    instance  : Inhabited (Syntax → StateT st MetaM (Expr × metaTy)) where
      default _ := pure (.const ``true [],metaUU [])

    partial def elabGATTy : Syntax → StateT st MetaM (Expr × metaTy)
    | `(gat_ty| U ) => do
        let TT ← getCurrentTel
        return (.const ``preUU [],metaUU TT)
    | `(gat_ty| $x:gat_tm ) => do
        let (t,mt,mX) ← elabGATTm x
        failIfNotU "Bad El" mt mX
        let T ← mkAppM ``preEL #[t]
        let TT ← getCurrentTel
        return (T,metaEl TT mt)
    | `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
        let domain ← elabGATArg T
        let (codomain,finalT) ← elabGATTy T'
        let result ← mkAppM  ``prePI #[domain,codomain]
        return (result,finalT)
    | `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
        let (tt1,mt1,mX1) ← elabGATTm t1
        let (tt2,mt2,mX2) ← elabGATTm t2
        let mX ← failIfBadEq mt1 mt2 mX1 mX2
        let T ← mkAppM ``preEQ #[tt1,tt2]
        let TT ← getCurrentTel
        return (T,metaEq TT mX mt1 mt2)
    | _ => throwError "TyFail"


    partial def elabGATCon_core : Syntax → StateT st MetaM Expr
    | `(con_inner| $rest:con_inner , $i:ident : $g:gat_ty ) => do
        let restCon ← elabGATCon_core rest
        setCurrentName i.getId.toString
        let (T,finalT) ← elabGATTy g
        let newCtx ← mkAppM ``preEXTEND #[restCon, T]
        extendMain finalT
        return newCtx
    | `(con_inner| $i:ident : $g:gat_ty ) => do
        setCurrentName i.getId.toString
        let (T,finalT) ← elabGATTy g
        let newCtx ← mkAppM ``preEXTEND #[.const ``preEMPTY [],T]
        extendMain finalT
        return newCtx
    | _ => throwError "Con_coreFail"



    partial def elabGATConData : Syntax → MetaM Expr
    | `(condata_outer| [GATdata| ] ) => do
        let emptyStrList ← mkListLit (.const ``String []) []
        let emptyLArgList ← mkListLit (.const ``metaArg []) []
        let res ← mkAppM ``GATdata.mk  #[.const ``preEMPTY [],emptyStrList,emptyLArgList]
        return res
    | `(condata_outer| [rawGAT| $s:con_inner ] ) => do
        let (resCon,VV) ← StateT.run (elabGATCon_core s) (stEmpty true)
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit VV.topnames)
        let telescopes ← List.mapM mkMetaTyLit VV.telescopes >>= mkListLit (.const ``metaOut [])
        let res ← mkAppM ``rawGAT.mk #[resCon,topList,telescopes]
        return res
    | `(condata_outer| [GATdata| $s:con_inner ] ) => do
        let (resCon,VV) ← StateT.run (elabGATCon_core s) (stEmpty false)
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit (List.reverse VV.topnames))
        let telescopes ← List.mapM mkMetaTyLit' (List.reverse VV.telescopes) >>= mkListLit (.const ``StringOptList [])
        let res ← mkAppM ``GATdata.mk #[resCon,topList,telescopes]
        return res
    | _ => throwError "ConFail"

  end mainFunctions

elab g:condata_outer : term => elabGATConData g
