import GeneralizedAlgebra.signature
import Lean

open Lean Elab Meta
open preTy preTm
open Std Format
open Nat


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

    inductive metaTyMarker : Type where
    | metaUU : metaTyMarker
    | metaEl : metaTm → metaTyMarker
    | metaEq : metaTm → metaTm → metaTm → metaTyMarker
    open metaTyMarker

    def metaTy : Type := metaTyMarker × List metaArg


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

    def extractTel : metaTy → List metaArg := Prod.snd

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

    def metaWkTy : metaTy → metaTy
    | (metaEl t, TT) => (metaEl (metaWkTm t), List.map metaWkArg TT)
    | (metaEq X s t,TT) => (metaEq (metaWkTm X) (metaWkTm s) (metaWkTm t),List.map metaWkArg TT)
    | (metaUU, TT) => (metaUU, List.map metaWkArg TT)

    def metaWkTySortOnly
    | (metaEl t, TT) => (metaEl t, List.map metaWkSortOnly TT)
    | (metaEq X s t, TT) => (metaEq (metaWkTm X) s t, List.map metaWkSortOnly TT)
    | (metaUU, TT) => (metaUU, List.map metaWkSortOnly TT)

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
    | (metaUU, TT) => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaOut' [])
        mkAppM ``Prod.mk #[mkStrLit "UU",mTT]
    | (metaEq X s t, TT) => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaOut' [])
        mkAppM ``Prod.mk #[mkStrLit $ "Eq _(" ++ metaTm.toString X ++")(" ++ metaTm.toString s ++ ") (" ++ metaTm.toString t ++ ")",mTT]
    | (metaEl t, TT) => do
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
    | (metaUU, TT) => mkListLit (.const ``StringOpt []) (List.map mkMetaArgLit' (List.reverse TT))
    | (metaEq _ _ _, TT) => mkListLit (.const ``StringOpt []) (List.map mkMetaArgLit' (List.reverse TT))
    | (metaEl _, TT) => mkListLit (.const ``StringOpt []) (List.map mkMetaArgLit' (List.reverse TT))
  end literals

end nouGATmeta

namespace elabState

  open nouGATmeta
  open metaTm metaTyMarker metaArg metaArgMarker

    structure st where
      (topnames : List String)
      (telescopes : List metaTy)
      (currentName : Option String)
      (currentTel : List metaArg)
      (rawMode : Bool)
      (currentCon : Expr)

    def stEmpty (raw : Bool) (startCtx : Expr) : st := ⟨[],[],none,[],raw,startCtx⟩

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
    | (metaEl mX, TT) => formatList ind ((List.map (text ∘ metaArgFormat current) (List.reverse TT)) ++ [text " ⊢ ",outername ++ " : " ++ (metaTmFormat current mX)])
    | (metaUU, TT) => formatList ind ((List.map (text ∘ metaArgFormat current) (List.reverse TT)) ++ [text " ⊢ ",outername ++ " : U"])
    | (metaEq _ ms mt, TT) => formatList ind ((List.map (text ∘ metaArgFormat current) (List.reverse TT)) ++ [text " ⊢ ",outername ++ " : " ++ (metaTmFormat current ms) ++ " = " ++ (metaTmFormat current mt)])

    def metaTyFormat (current : st) (theTy : metaTy) (outername := "_") : Format := match theTy with
    | (metaEl mX, TT) => (String.intercalate ", " (List.map (metaArgFormat current) (List.reverse TT))) ++ " ⊢ " ++ outername ++ " : " ++ (metaTmFormat current mX)
    | (metaUU, TT) => (String.intercalate ", " (List.map (metaArgFormat current) (List.reverse TT))) ++ " ⊢ " ++ outername ++ " : U"
    | (metaEq _ ms mt, TT) => (String.intercalate ", " (List.map (metaArgFormat current) (List.reverse TT))) ++ " ⊢ " ++ outername ++ " : " ++ (metaTmFormat current ms) ++ " = " ++ (metaTmFormat current mt)

    def previousFormat (current : st) : String × metaTy → Format
    | (s,T) => metaTyFormat current T s

  end toString

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

  section extend
    def extendMain (finalT : metaTyMarker) (extendOp newTy : Expr): StateT st MetaM Unit := do
      let current ← get
      let theName ← optFail "getting name for extension" current.currentName
      set $ st.mk (theName::current.topnames) ((finalT,current.currentTel)::current.telescopes) none [] current.rawMode (mkAppN extendOp #[current.currentCon,newTy])

    def extendTel (newArgMark : metaArgMarker) : StateT st MetaM Unit := do
      let current ← get
      let gIndex := current.topnames.length
      let newArg := match newArgMark with
        | mkImpl i mX => metaImpl i (metaLOC gIndex 0) (localWkTm mX)
        | mkExpl i mX => metaExpl i (metaLOC gIndex 0) (localWkTm mX)
        | mkAnon mX => metaAnon (metaLOC gIndex 0) (localWkTm mX)
      set (st.mk current.topnames current.telescopes current.currentName (newArg::List.map localWkArg current.currentTel) current.rawMode current.currentCon)
  end extend

  section access

    def findIdxElem {α} (p : α → Bool) (l : List α) : Option (Nat × α) := do
    let elem ← List.find? p l
    let idx ← List.findIdx? p l
    return (idx,elem)

    def varTelLkup_core (key : String) : StateT st MetaM (Option (metaTm × metaTy × Nat)) := do
        let current ← get
        let gIndex := current.topnames.length
        match findIdxElem (argMatch key) current.currentTel with
        | some (idx,a) => return some (metaLOC gIndex idx,(metaEl (extractMetaSort a),[]),idx)
        | none => match findIdxElem (λ (s,_) => s == key) (List.zip current.topnames current.telescopes) with
          | some (idx,_,T) => return (metaGLOB (gIndex - idx - 1),T,idx + current.currentTel.length)
          | none => return none

    def setCurrentName (theName : String) : StateT st MetaM Unit := do
      let current ← get
      set (st.mk current.topnames current.telescopes (some theName) current.currentTel current.rawMode current.currentCon)

    def getCurrentTel : StateT st MetaM (List metaArg) := do
      let current ← get
      return current.currentTel

    def getCurrentCon : StateT st MetaM Expr := do
      let current ← get
      return current.currentCon

    def varTelLkup (key : String) : StateT st MetaM (metaTm × metaTy × Nat) := do
        let resO ← varTelLkup_core key
        match resO with
          | some z => return z
          | none => elabFail "" (errorCode.errUnknownVar key)
  end access

end elabState

namespace elaborator

    open nouGATmeta
    open elabState
    open metaTm metaArg metaArgMarker metaTyMarker
    open Nat

  section theSyntax

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

  end theSyntax

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
    | (metaUU, args) => do
        let (rest,arg) ← optFail "Tried to perform dummy substitution" (initLast args)
        let s := extractMetaTm arg
        return ((metaUU, (List.map (metaSubstArg s t) rest)),arg)
    | (metaEl finalT, args) => do
        let (rest,arg) ← optFail "Tried to perform dummy substitution" (initLast args)
        let s := extractMetaTm arg
        return ((metaEl (metaSubstTm s t finalT), List.map (metaSubstArg s t) rest),arg)
    | (metaEq finalT ms mt, args) => do
        let (rest,arg) ← optFail "Tried to perform dummy substitution" (initLast args)
        let s := extractMetaTm arg
        return ((metaEq (metaSubstTm s t finalT) (metaSubstTm s t ms) (metaSubstTm s t mt), List.map (metaSubstArg s t) rest),arg)

    partial def metaTyApp (fnTm : metaTm) (fnTy : metaTy) (argTm : metaTm) (argTy : metaTy) : StateT st MetaM metaTy := match (fnTy,argTy) with
    | (_, metaUU, _) => elabFail "Bad argument" (errorCode.errKind argTm argTy "a sort" "an element")
    | (_,  metaEq _ _ _, _) => elabFail "Bad argument" (errorCode.errKind argTm argTy "an equation" "an element")
    | (_,  metaEl  _,(_::_)) => elabFail "Bad argument" (errorCode.errOpen argTm argTy)
    | ((_, []), _) => elabFail "Bad function" (errorCode.errTooManyArgs fnTm fnTy)
    | ((metaUU, args), metaEl y, []) => do
        let (finalT',x) ← locSubstTy argTm (metaUU, args)
        metaTyMatch "Bad application" x y finalT'
    | ((metaEl finalT,args), metaEl y, []) => do
        let (finalT',x) ← locSubstTy argTm (metaEl finalT, args)
        metaTyMatch "Bad application" x y finalT'
    | ((metaEq finalT ms mt, args) ,  metaEl y, []) => do
        let (finalT',x) ← locSubstTy argTm (metaEq finalT ms mt,args)
        metaTyMatch "Bad application" x y finalT'


    partial def failIfBadTransp (tm1 tm2 : metaTm) (T1 T2 : metaTy) : StateT st MetaM metaTy := match (T1,T2) with
    | ((metaEq _ ms mt, []), metaEl mq, []) => return (metaEl $ metaSubstTm ms mt mq, [])
    | ((metaEq _ _ _, (_::_)), metaEl _, _) => elabFail "Bad transport" (errorCode.errOpen tm1 T1)
    | ((metaEq _ _ _, []), metaEl _, _) => elabFail "Bad transport" (errorCode.errOpen tm2 T2)
    | ((metaEl _, _) , _) => elabFail "Bad transport" (errorCode.errKind tm1 T1 "an element" "an equality")
    | ((metaUU, _) , _) =>  elabFail "Bad transport" (errorCode.errKind tm1 T1 "a sort" "an equality")
    | (_, metaEq _ _ _, _)  => elabFail "Bad transport" (errorCode.errKind tm2 T2 "an equality" "an element")
    | (_, metaUU, _) => elabFail "Bad transport" (errorCode.errKind tm2 T2 "a sort" "an element")

    partial def failIfNotU (suberror : String) (theTm : metaTm) (theTy : metaTy) : StateT st MetaM Unit := match theTy with
    | (metaUU, []) => return ()
    | (metaUU, _) => elabFail suberror (errorCode.errOpen theTm theTy)
    | (metaEq _ _ _, _) => elabFail suberror (errorCode.errKind theTm theTy "an equality" "a sort")
    | (metaEl _, _)  => elabFail suberror (errorCode.errKind theTm theTy "an element" "a sort")

    partial def failIfBadEq (tm1 tm2 : metaTm) (T1 T2 : metaTy) : StateT st MetaM metaTm := match (T1,T2) with
    | ((metaEl mX1, []), metaEl mX2, []) => if mX1 = mX2 then return mX1 else
    elabFail "Bad eq" (errorCode.errType2 "LHS" mX1 "RHS" mX2)
    | ((metaEl _,  (_::_)), metaEl _, _) => elabFail "Bad eq" (errorCode.errOpen tm1 T1)
    | ((metaEl _, _), metaEl _, _) => elabFail "Bad eq" (errorCode.errOpen tm2 T2)
    | ((metaUU, _), _) => elabFail "Bad eq" (errorCode.errKind tm1 T1 "a sort" "an element")
    | ((metaEq _ _ _, _), _) => elabFail "Bad eq" (errorCode.errKind tm1 T1 "an equality" "an element")
    | (_, metaUU, _) => elabFail "Bad eq" (errorCode.errKind tm2 T2 "a sort" "an element")
    | (_, metaEq _ _ _, _) => elabFail "Bad eq" (errorCode.errKind tm2 T2 "an equality" "an element")

  end failureHelpers

  section eliminator

    structure eliminator_inner where
      (Con_D : Type)
      (Ty_D : Con_D → Type)
      (Tm_D : Con_D → Type)
      (Empty_D : Con_D)
      (Extend_D : (Γ : Con_D) → Ty_D Γ → Con_D)
      (UU_D : (Γ : Con_D) → Ty_D Γ)
      (El_D : (Γ : Con_D) → Tm_D Γ → Ty_D Γ)
      (Pi_D : (Γ : Con_D) → (X : Tm_D Γ) → Ty_D (Extend_D Γ (El_D Γ X)) → Ty_D Γ)
      (Eq_D : (Γ : Con_D) → Tm_D Γ → Tm_D Γ → Ty_D Γ)
      (Var_D : (Γ : Con_D) → Nat → Tm_D Γ)
      (App_D : (Γ : Con_D) → Tm_D Γ → Tm_D Γ → Tm_D Γ)
      (Transp_D : (Γ : Con_D) → Tm_D Γ → Tm_D Γ → Tm_D Γ)

    structure eliminator extends eliminator_inner where
      (Output : Type)
      (mkOutput : Con_D → List String → List (List (Option String)) → Output)

    def eliminator_outer (inn : eliminator_inner) : Type 1 := @Sigma Type (λ O => inn.Con_D → List String → List (List (Option String)) → O)

    def elimProduct_outer {inn : eliminator_inner} (EO1 EO2 : eliminator_outer inn) : eliminator_outer inn :=
      ⟨ EO1.1 × EO2.1, λ Γ topnames telescopes => (EO1.2 Γ topnames telescopes,EO2.2 Γ topnames telescopes)⟩

    def elimProduct_outer_post {inn : eliminator_inner} (EO : eliminator_outer inn) {Output' : Type} (f : EO.1 → Output') : eliminator_outer inn :=
      ⟨ Output', λ Γ topnames telescopes => f (EO.2 Γ topnames telescopes)⟩

    def toEliminator {inn : eliminator_inner} (outt : eliminator_outer inn) : eliminator := ⟨inn, outt.1,outt.2⟩

    def elimProduct_inner (E1 E2 : eliminator_inner) : eliminator_inner := ⟨
        E1.Con_D × E2.Con_D,
        λ (Γ1,Γ2) => E1.Ty_D Γ1 × E2.Ty_D Γ2,
        λ (Γ1,Γ2) => E1.Tm_D Γ1 × E2.Tm_D Γ2,
        (E1.Empty_D,E2.Empty_D),
        λ (x1,x2) (y1,y2) => (E1.Extend_D x1 y1,E2.Extend_D x2 y2),
        λ (Γ1,Γ2) => (E1.UU_D Γ1,E2.UU_D Γ2),
        λ (Γ1,Γ2) (x1,x2) => (E1.El_D Γ1 x1,E2.El_D Γ2 x2),
        λ (Γ1,Γ2) (x1,x2) (y1,y2) => (E1.Pi_D Γ1 x1 y1,E2.Pi_D Γ2 x2 y2),
        λ (Γ1,Γ2) (x1,x2) (y1,y2) => (E1.Eq_D Γ1 x1 y1,E2.Eq_D Γ2 x2 y2),
        λ (Γ1,Γ2) n => (E1.Var_D Γ1 n,E2.Var_D Γ2 n),
        λ (Γ1,Γ2) (x1,x2) (y1,y2) => (E1.App_D Γ1 x1 y1,E2.App_D Γ2 x2 y2),
        λ (Γ1,Γ2) (x1,x2) (y1,y2) => (E1.Transp_D Γ1 x1 y1,E2.Transp_D Γ2 x2 y2)
      ⟩
    def elimProduct (E1 E2 : eliminator) : eliminator := ⟨
      elimProduct_inner E1.toeliminator_inner E2.toeliminator_inner,
      E1.Output × E2.Output,
      λ (x1,x2) topnames telescopes => (E1.mkOutput x1 topnames telescopes, E2.mkOutput x2 topnames telescopes)
    ⟩
    def elimProduct' (E1 E2 : eliminator) (Output' : Type) (mkOutput' : E1.Con_D → E2.Con_D → List String → List (List (Option String)) → Output'): eliminator := ⟨
      elimProduct_inner E1.toeliminator_inner E2.toeliminator_inner,
      Output',
      λ (x1,x2) => mkOutput' x1 x2
    ⟩
    def elimProduct_post (Elim : eliminator) {Output' : Type} (f : Elim.Output → Output') : eliminator :=
      ⟨ Elim.toeliminator_inner, Output',
        λ Γ topnames telescopes => f (Elim.mkOutput Γ topnames telescopes)⟩



    def litToInner : Expr → Expr := .app (.const ``eliminator.toeliminator_inner [])
    def litEmpty_D : Expr → Expr := .app (.const ``eliminator_inner.Empty_D []) ∘ litToInner
    def litExtend_D : Expr → Expr := .app (.const ``eliminator_inner.Extend_D []) ∘ litToInner
    def litUU_D : Expr → Expr := .app (.const ``eliminator_inner.UU_D []) ∘ litToInner
    def litEl_D : Expr → Expr := .app (.const ``eliminator_inner.El_D []) ∘ litToInner
    def litPi_D : Expr → Expr := .app (.const ``eliminator_inner.Pi_D []) ∘ litToInner
    def litEq_D : Expr → Expr := .app (.const ``eliminator_inner.Eq_D []) ∘ litToInner
    def litApp_D : Expr → Expr := .app (.const ``eliminator_inner.App_D []) ∘ litToInner
    def litTransp_D : Expr → Expr := .app (.const ``eliminator_inner.Transp_D []) ∘ litToInner
    def litVar_D : Expr → Expr := .app (.const ``eliminator_inner.Var_D []) ∘ litToInner

    def litMk : Expr → Expr := .app (.const ``eliminator.mkOutput [])

    def mkLitElim (litElim : Expr): Expr :=
      mkAppN (.const ``eliminator.mk []) #[
        mkAppN (.const ``eliminator_inner.mk []) #[
          .app (.const ``eliminator_inner.Con_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Ty_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Tm_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Empty_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Extend_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.UU_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.El_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Pi_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Eq_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Var_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.App_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Transp_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim)],
        .app (.const ``eliminator.Output []) litElim,
        .app (.const ``eliminator.mkOutput []) litElim
      ]
  end eliminator

  section mainFunctions


    instance  : Inhabited (Syntax → StateT st MetaM (Expr × metaTm × metaTy)) where
      default _ := pure (.const ``true [],metaGLOB 0,metaUU, [])

    partial def elabGATTm (Elim : Expr) : Syntax → StateT st MetaM (Expr × metaTm × metaTy)
    | `(gat_tm| ( $g:gat_tm ) ) => elabGATTm Elim g
    | `(gat_tm| $g1:gat_tm $g2:gat_tm ) => do
          let (t1,mt1,mA1) ← elabGATTm Elim g1
          let (t2,mt2,mA2) ← elabGATTm Elim g2
          let mRes ← metaTyApp mt1 mA1 mt2 mA2
          let Γ ← getCurrentCon
          return (mkAppN (litApp_D Elim) #[Γ,t1,t2], metaAPP mt1 mt2,mRes)
    | `(gat_tm| $i:ident ) => do
          let (mb,m,b) ← varTelLkup i.getId.toString
          let Γ ← getCurrentCon
          return (mkAppN (litVar_D Elim) #[Γ,mkNatLit b],mb,m)
    | `(gat_tm| $g1 #⟨ $g2 ⟩ ) => do
          let (t1,mt1,mX1) ← elabGATTm Elim g1
          let (t2,mt2,mX2) ← elabGATTm Elim g2
          let mresT ← failIfBadTransp mt2 mt1 mX2 mX1
          let Γ ← getCurrentCon
          return (mkAppN (litTransp_D Elim) #[Γ,t2,t1],metaTRANSP mt2 mt1,mresT)
    | _ => throwError "TmFail"

    partial def elabGATArg (Elim : Expr) : Syntax → StateT st MetaM Expr
    | `(gat_arg| ( $i:ident : $g:gat_tm ) ) => do
      let (t,mt,mX) ← elabGATTm Elim g
      failIfNotU "Failed to create argument" mt mX
      extendTel (mkExpl i.getId.toString mt)
      return t
    | `(gat_arg| ( _ : $g:gat_tm ) ) => do
      let (t,mt,mX) ← elabGATTm Elim g
      failIfNotU "Failed to create argument" mt mX
      extendTel (mkAnon mt)
      return t
    | `(gat_arg| $g:gat_tm ) => do
      let (t,mt,mX) ← elabGATTm Elim g
      failIfNotU "Failed to create argument" mt mX
      extendTel (mkAnon mt)
      return t
    | _ => throwError "ArgFail"

    instance  : Inhabited (Syntax → StateT st MetaM (Expr × metaTyMarker)) where
      default _ := pure (.const ``true [],metaUU)

    partial def elabGATTy (Elim : Expr) : Syntax → StateT st MetaM (Expr × metaTyMarker)
    | `(gat_ty| U ) => do
        let Γ ← getCurrentCon
        return (mkAppN (litUU_D Elim) #[Γ],metaUU)
    | `(gat_ty| $x:gat_tm ) => do
        let (t,mt,mX) ← elabGATTm Elim x
        failIfNotU "Bad El" mt mX
        let Γ ← getCurrentCon
        return (mkAppN (litEl_D Elim) #[Γ,t],metaEl mt)
    | `(gat_ty| $T:gat_arg ⇒ $T':gat_ty) => do
        let domain ← elabGATArg Elim T
        let (codomain,finalT) ← elabGATTy Elim T'
        let Γ ← getCurrentCon
        return (mkAppN (litPi_D Elim) #[Γ,domain,codomain],finalT)
    | `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
        let (tt1,mt1,mX1) ← elabGATTm Elim t1
        let (tt2,mt2,mX2) ← elabGATTm Elim t2
        let mX ← failIfBadEq mt1 mt2 mX1 mX2
        let Γ ← getCurrentCon
        return (mkAppN (litEq_D Elim) #[Γ,tt1,tt2],metaEq mX mt1 mt2)
    | _ => throwError "TyFail"

    def GlobalRawErrorMsg : Bool := false

    partial def elabGATCon_core (Elim : Expr) : Syntax → StateT st MetaM Unit
    | `(con_inner| $rest:con_inner , $i:ident : $g:gat_ty ) => do
        elabGATCon_core Elim rest
        setCurrentName i.getId.toString
        let (T,finalT) ← elabGATTy Elim g
        extendMain finalT (litExtend_D Elim) T
    | `(con_inner| $i:ident : $g:gat_ty ) => do
        setCurrentName i.getId.toString
        let (T,finalT) ← elabGATTy Elim g
        extendMain finalT (litExtend_D Elim) T
    | _ => throwError "Con_coreFail"

    def elabEmptyGAT (Elim : Expr) : MetaM Expr :=  do
        let emptyStrList ← mkListLit (.const ``String []) []
        let emptyLArgList ← mkListLit (.const ``metaArg []) []
        return mkAppN (litMk Elim) #[litEmpty_D Elim,emptyStrList,emptyLArgList]

    def elabNonemptyGAT (Elim : Expr) (s : Syntax) : MetaM Expr := do
        let (_,VV) ← StateT.run (elabGATCon_core Elim s) (stEmpty GlobalRawErrorMsg (litEmpty_D Elim))
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit (List.reverse VV.topnames))
        let telescopes ← List.mapM mkMetaTyLit' (List.reverse VV.telescopes) >>= mkListLit (.const ``StringOptList [])
        return mkAppN (litMk Elim) #[VV.currentCon,topList,telescopes]

  end mainFunctions
end elaborator

namespace basicEliminators

open preTy preTm
open elaborator

  def preElim_inner : eliminator_inner := ⟨
      preCon,
      λ _ => preTy,
      λ _ => preTm,
      preEMPTY,
      preEXTEND,
      λ _ => preUU,
      λ _ => preEL,
      λ _ => prePI,
      λ _ => preEQ,
      λ _ => preVAR,
      λ _ => preAPP,
      λ _ => preTRANSP⟩

  def GATdataElim_outer : eliminator_outer preElim_inner := ⟨ GATdata, GATdata.mk ⟩
  def GATdataElim : eliminator := toEliminator GATdataElim_outer

  def justGATElim : eliminator := ⟨preElim_inner, preCon, λ Γ _ _ => Γ⟩

-- #check (GATdata,GATdata.mk) : @Sigma Type (λ O => preCon → List String → List (List (Option String)) → O)
  -- def preElimProduct (Out1 : Type)

  declare_syntax_cat condata_outer
  syntax "[GATdata|" "]" : condata_outer
  syntax "[GATdata|" con_inner "]" : condata_outer
  syntax "[justGAT|" "]" : condata_outer
  syntax "[justGAT|" con_inner "]" : condata_outer

end basicEliminators
