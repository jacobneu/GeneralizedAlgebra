import GeneralizedAlgebra.signature
import Lean

open Lean Elab Meta
open preTy preTm
open Std Format
open Nat
open ArgMarker


namespace nouGATmeta

  -- Datatypes
    inductive metaTm : Type where
    | metaGLOB : Nat → metaTm
    | metaLOC : Nat → Nat → metaTm
    | metaAPP : metaTm → metaTm → metaTm
    | metaTRANSP : metaTm → metaTm → metaTm
    open metaTm

    -- inductive metaArgMarker : Type where
    -- | mkImpl : String → metaTm → metaArgMarker
    -- | mkExpl : String → metaTm → metaArgMarker
    -- | mkAnon : metaTm → metaArgMarker
    -- open metaArgMarker

    -- inductive metaArg : Type where
    -- | metaImpl : String → metaTm → metaTm → metaArg
    -- | metaExpl : String → metaTm → metaTm → metaArg
    -- | metaAnon : metaTm → metaTm → metaArg
    -- open metaArg
    def metaArgMarker : Type := ArgMarker × metaTm
    def metaArg : Type := ArgMarker × metaTm × metaTm

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

    def metaTm.toString' : metaTm → String
    | metaGLOB n => "GLOB " ++ Nat.repr n
    | metaLOC g b => "LOC (" ++ Nat.repr g ++ "," ++ Nat.repr b ++ ")"
    | metaAPP m1 m2 => mkParen m1.toString' ++ " @ " ++ mkParen m2.toString'
    | metaTRANSP m1 m2 => "TRANSP " ++ mkParen m1.toString' ++ " " ++ mkParen m2.toString'

    def metaArg.toString : metaArg → String
    | (Impl i, _, _) => "Impl(" ++ i ++ ")"
    | (Expl i, _, _) => "Expl("++ i ++ ")"
    | (Anon, _, _) => "Anon"

    def metaArg.toString' : metaArg → String
    | (Impl i, mt, mX) => "{"++ i ++ "=" ++ mkParen mt.toString' ++ " : " ++ mkParen mX.toString' ++ "}"
    | (Expl i, mt, mX) => "("++ i ++ "=" ++ mkParen mt.toString' ++ " : " ++ mkParen mX.toString' ++ ")"
    | (Anon, mt, mX) => "(_=" ++ mkParen mt.toString' ++ " : " ++ mkParen mX.toString' ++ ")"

    def metaTy.toFormat : metaTy → Format
    | (metaUU,args) => (text  "metaUU")
          ++ (nest 3 <| (align true) ++ "[" ++ String.intercalate ", " (List.map metaArg.toString' args) ++ "]")
    | (metaEl mX,args) => (text "metaEl " ++ mkParen mX.toString')
          ++ (nest 3 <| (align true) ++ "[" ++ String.intercalate ", " (List.map metaArg.toString' args) ++ "]")
    | (metaEq mX ms mt,args) =>  (text $ "metaEq " ++ String.intercalate " " [mkParen mX.toString',mkParen ms.toString',mkParen mt.toString'])
          ++ (nest 3 <| (align true) ++ "[" ++ String.intercalate ", " (List.map metaArg.toString' args) ++ "]")

    instance : Repr metaTy := ⟨λ t _ => metaTy.toFormat t⟩
  end toString

  section extractionComparison
  -- Extraction & comparison
    def extractMetaTm (mA : metaArg) : metaTm := mA.2.1

    def extractMetaSort (mA : metaArg) : metaTm := mA.2.2

    def extractTel : metaTy → List metaArg := Prod.snd

    def extractName (mA : metaArg) : String := mA.1.getName

    def argMatch (key : String) : metaArg → Bool
    | (Impl i, _, _) => key=i
    | (Expl i, _, _) => key=i
    | (Anon, _, _) => false
  end extractionComparison

  section weakening
  -- Global Weakening functions
    def metaWkTm
    | metaGLOB b => metaGLOB (succ b)
    | metaLOC g b => metaLOC (succ g) b
    | metaAPP f t => metaAPP (metaWkTm f) (metaWkTm t)
    | metaTRANSP f t => metaTRANSP (metaWkTm f) (metaWkTm t)

    def metaWkArg : metaArg → metaArg
    | (mA,mt, mX) => (mA, metaWkTm mt, metaWkTm mX)

    def metaWkSortOnly : metaArg → metaArg
    | (mA,mt, mX) => (mA, mt, metaWkTm mX)

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

    def localWkSortOnly : metaArg → metaArg
    | (mA,mt, mX) => (mA, mt, localWkTm mX)

    def localWkArg : metaArg → metaArg
    | (mA,mt, mX) => (mA, localWkTm mt, localWkTm mX)

  end weakening

  section substitution
  -- Substitution functions
    def metaSubstTm (s t q : metaTm) : metaTm := if q = s then t else
    match q with
    | metaAPP f x => metaAPP (metaSubstTm s t f) (metaSubstTm s t x)
    | metaTRANSP p x => metaTRANSP (metaSubstTm s t p) (metaSubstTm s t x)
    | z => z

    def metaSubstArg (s t : metaTm) : metaArg → metaArg
    | (mA, mt, mX) => (mA, metaSubstTm s t mt, metaSubstTm s t mX)

  end substitution

  section literals
  -- Make literal for rawGAT
    def mkMetaTmLit : metaTm → Expr -- :: metaTm
    | metaLOC g b => mkAppN (.const ``metaLOC []) #[mkNatLit g,mkNatLit b]
    | metaGLOB b => .app (.const ``metaGLOB []) (mkNatLit b)
    | metaAPP m1 m2 => mkApp2 (.const ``metaAPP []) (mkMetaTmLit m1) (mkMetaTmLit m2)
    | metaTRANSP m1 m2 => mkApp2 (.const ``metaTRANSP []) (mkMetaTmLit m1) (mkMetaTmLit m2)

    def ArgMarker.mkLit : ArgMarker → Expr
    | Anon => .const ``Anon []
    | Expl i => .app (.const ``Expl []) (mkStrLit i)
    | Impl i => .app (.const ``Impl []) (mkStrLit i)

    def mkMetaArgLit : metaArg → MetaM Expr -- :: metaArg
    | (mA, mt, mX) => do
        let mSnd ← mkAppM ``Prod.mk #[mkMetaTmLit mt,mkMetaTmLit mX]
        mkAppM ``Prod.mk #[ArgMarker.mkLit mA,mSnd]

    def mkMetaTyLit : metaTy → MetaM Expr -- :: metaTy
    | (metaUU, TT) => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaArg [])
        mkAppM ``Prod.mk #[.const ``metaUU [],mTT]
    | (metaEq X s t, TT) => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaArg [])
        mkAppM ``Prod.mk #[mkAppN (.const ``metaEq []) #[mkMetaTmLit X,mkMetaTmLit s,mkMetaTmLit t],mTT]
    | (metaEl t, TT) => do
        let mTT ← List.mapM mkMetaArgLit TT >>= mkListLit (.const ``metaArg [])
        mkAppM ``Prod.mk #[.app (.const ``metaEl []) (mkMetaTmLit t),mTT]

    def StringBool : Type := String × Bool
    def mkStringBool (s : String) (b : Bool) : StringBool := (s,b)

  -- Make literal for GATdata
    def mkMetaArgLit' : metaArg → Expr -- :: ArgMarker
    | (mA,_,_) => ArgMarker.mkLit mA


    def mkMetaTyLit' : metaTy → MetaM Expr -- :: List ArgMarker
    | (metaUU, TT) => mkListLit (.const ``ArgMarker []) (List.map mkMetaArgLit' (List.reverse TT))
    | (metaEq _ _ _, TT) => mkListLit (.const ``ArgMarker []) (List.map mkMetaArgLit' (List.reverse TT))
    | (metaEl _, TT) => mkListLit (.const ``ArgMarker []) (List.map mkMetaArgLit' (List.reverse TT))
  end literals

end nouGATmeta

namespace elabState

  open nouGATmeta
  open metaTm metaTyMarker metaArg

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
    | metaTRANSP m1 m2 =>  mkParen (metaTmFormat current m2) ++ " #⟨" ++ metaTmFormat current m1 ++ "⟩"

    def metaArgFormat (current : st) : metaArg → String
    | (mA,mt,mX) => (if current.rawMode then mA.map (· ++ "=" ++ mt.toString) else mA).toString (metaTmFormat current mX)

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


  inductive argInstr : Type where
  | firstExpl : argInstr
  | firstImpl : argInstr
  open argInstr

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
    | errImplExplMismatch : argInstr → errorCode
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
    | errImplExplMismatch firstImpl =>
        return (text $ suberror ++ ": Looked for implicit argument, found none")
    | errImplExplMismatch firstExpl =>
        return (text $ suberror ++ ": Looked for explicit argument, found none")





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
    def extendMain (finalT : metaTyMarker) : StateT st MetaM Unit := do
      let current ← get
      let theName ← optFail "getting name for extension" current.currentName
      set (st.mk (theName::current.topnames) ((finalT,current.currentTel)::current.telescopes) none [] current.rawMode)

    def extendTel (newArgMark : metaArgMarker) : StateT st MetaM Unit := do
      let current ← get
      let gIndex := current.topnames.length
      let newArg := (newArgMark.1,metaLOC gIndex 0,localWkTm newArgMark.2)
      set (st.mk current.topnames current.telescopes current.currentName (newArg::List.map localWkArg current.currentTel) current.rawMode)
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
      set (st.mk current.topnames current.telescopes (some theName) current.currentTel current.rawMode)

    def getCurrentTel : StateT st MetaM (List metaArg) := do
      let current ← get
      return current.currentTel

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
    open metaTm metaArg metaTyMarker
    open Nat

  section theSyntax

    declare_syntax_cat gat_ty
    syntax "U"       : gat_ty
    syntax "(" gat_ty ")" : gat_ty

    declare_syntax_cat gat_tm
    syntax ident     : gat_tm
    syntax "(" gat_tm ")" : gat_tm
    -- declare_syntax_cat gat_input
    -- syntax gat_tm : gat_input
    -- syntax "{" gat_tm "}" : gat_input
    syntax:60 gat_tm:60 gat_tm:61 : gat_tm
    syntax:60 gat_tm:60 "{" gat_tm:60 "}" : gat_tm
    syntax:58 gat_tm:58  "#⟨" gat_tm:59 "⟩" : gat_tm
    syntax gat_tm : gat_ty
    syntax gat_tm " ≡ " gat_tm : gat_ty

    declare_syntax_cat gat_decl
    syntax ident+ ":" gat_ty : gat_decl

    declare_syntax_cat gat_arg
    declare_syntax_cat gat_underscore
    syntax "_" : gat_underscore
    syntax "(" ident+ ":" gat_tm ")" : gat_arg
    syntax "(" gat_underscore+ ":" gat_tm ")" : gat_arg
    syntax "{" ident+ ":" gat_tm "}" : gat_arg
    syntax gat_tm : gat_arg

    syntax gat_arg "⇒" gat_ty : gat_ty

    declare_syntax_cat con_inner
    syntax gat_decl,* : con_inner
    -- syntax "include" ident "as" "(" ident_list ");" con_inner : con_inner

  end theSyntax

  -- Failure-prone helper functions
  section failureHelpers

    def initLast {A : Type} (l : List A) : Option (List A × A) := do
        let last ← List.getLast? l
        let init := List.dropLast l
        return (init,last)

    def metaTyMatch (suberror : String): metaArg → metaTm → metaTy → StateT st MetaM metaTy
    | (_,_,m1), m2, res => if m1 = m2 then return res else elabFail suberror (errorCode.errType m1 m2)



    open argInstr
    def splitArgs : argInstr → List metaArg → StateT st MetaM (List metaArg × metaArg)
    | argI, [] => elabFail "Cannot substitute argument" (errorCode.errImplExplMismatch argI)
    | argI, firstArg :: rest => match (argI,firstArg.1) with
      | (firstExpl,Impl _) => do
          let (resList,resArg) ← splitArgs argI rest
          return (firstArg::resList,resArg)
      | (firstImpl,Expl _) => do
          let (resList,resArg) ← splitArgs argI rest
          return (firstArg::resList,resArg)
      | (firstImpl,Anon) => do
          let (resList,resArg) ← splitArgs argI rest
          return (firstArg::resList,resArg)
      | _ => return (rest,firstArg)

    def locSubstTy (argI : argInstr) (t : metaTm) : metaTy → StateT st MetaM (metaTy × metaArg)
    | (metaUU, args) => do
        let (revRest,arg) ← splitArgs argI (List.reverse args)
        let rest := List.reverse revRest
        let s := extractMetaTm arg
        return ((metaUU, (List.map (metaSubstArg s t) rest)),arg)
    | (metaEl finalT, args) => do
        let (revRest,arg) ← splitArgs argI (List.reverse args)
        let rest := List.reverse revRest
        let s := extractMetaTm arg
        return ((metaEl (metaSubstTm s t finalT), List.map (metaSubstArg s t) rest),arg)
    | (metaEq finalT ms mt, args) => do
        let (revRest,arg) ← splitArgs argI (List.reverse args)
        let rest := List.reverse revRest
        let s := extractMetaTm arg
        return ((metaEq (metaSubstTm s t finalT) (metaSubstTm s t ms) (metaSubstTm s t mt), List.map (metaSubstArg s t) rest),arg)

    partial def metaTyApp (argI : argInstr) (fnTm : metaTm) (fnTy : metaTy) (argTm : metaTm) (argTy : metaTy) : StateT st MetaM metaTy := match (fnTy,argTy) with
    | (_, metaUU, _) => elabFail "Bad argument" (errorCode.errKind argTm argTy "a sort" "an element")
    | (_,  metaEq _ _ _, _) => elabFail "Bad argument" (errorCode.errKind argTm argTy "an equation" "an element")
    | (_,  metaEl  _,(_::_)) => elabFail "Bad argument" (errorCode.errOpen argTm argTy)
    | ((_, []), _) => elabFail "Bad function" (errorCode.errTooManyArgs fnTm fnTy)
    | ((metaUU, args), metaEl y, []) => do
        let (finalT',x) ← locSubstTy argI argTm (metaUU, args)
        metaTyMatch "Bad application" x y finalT'
    | ((metaEl finalT,args), metaEl y, []) => do
        let (finalT',x) ← locSubstTy argI argTm (metaEl finalT, args)
        metaTyMatch "Bad application" x y finalT'
    | ((metaEq finalT ms mt, args) ,  metaEl y, []) => do
        let (finalT',x) ← locSubstTy argI argTm (metaEq finalT ms mt,args)
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
      (Ty_D : Type)
      (Tm_D : Type)
      (Empty_D : Con_D)
      (Extend_D : Con_D → Ty_D → Con_D)
      (UU_D : Ty_D)
      (El_D : Tm_D → Ty_D)
      (Pix_D : Tm_D → Ty_D → Ty_D)
      (Pii_D : Tm_D → Ty_D → Ty_D)
      (Eq_D : Tm_D → Tm_D → Ty_D)
      (Var_D : Nat → Tm_D)
      (Appx_D : Tm_D → Tm_D → Tm_D)
      (Appi_D : Tm_D → Tm_D → Tm_D)
      (Transp_D : Tm_D → Tm_D → Tm_D)

    structure eliminator extends eliminator_inner where
      (Output : Type)
      (mkOutput : Con_D → List String → List (List ArgMarker) → Output)

    def dummy : eliminator := ⟨⟨
      Unit, Unit, Unit, (), λ _ _ => (), (), λ _ => (), λ _ _ => (), λ _ _ => (), λ _ _ => (), λ _ => (), λ _ _ => (), λ _ _ => (), λ _ _ => ()
    ⟩, Unit, λ _ _ _ => ()⟩

    def eliminator_outer (inn : eliminator_inner) : Type 1 := @Sigma Type (λ O => inn.Con_D → List String → List (List ArgMarker) → O)

    def elimProduct_outer {inn : eliminator_inner} (EO1 EO2 : eliminator_outer inn) : eliminator_outer inn :=
      ⟨ EO1.1 × EO2.1, λ Γ topnames telescopes => (EO1.2 Γ topnames telescopes,EO2.2 Γ topnames telescopes)⟩

    def elimProduct_outer_post {inn : eliminator_inner} (EO : eliminator_outer inn) {Output' : Type} (f : EO.1 → Output') : eliminator_outer inn :=
      ⟨ Output', λ Γ topnames telescopes => f (EO.2 Γ topnames telescopes)⟩

    def toEliminator {inn : eliminator_inner} (outt : eliminator_outer inn) : eliminator := ⟨inn, outt.1,outt.2⟩

    def elimProduct_inner (E1 E2 : eliminator_inner) : eliminator_inner := ⟨
        E1.Con_D × E2.Con_D,
        E1.Ty_D × E2.Ty_D,
        E1.Tm_D × E2.Tm_D,
        (E1.Empty_D,E2.Empty_D),
        λ (x1,x2) (y1,y2) => (E1.Extend_D x1 y1,E2.Extend_D x2 y2),
        (E1.UU_D,E2.UU_D),
        λ (x1,x2) => (E1.El_D x1,E2.El_D x2),
        λ (x1,x2) (y1,y2) => (E1.Pix_D x1 y1,E2.Pix_D x2 y2),
        λ (x1,x2) (y1,y2) => (E1.Pii_D x1 y1,E2.Pii_D x2 y2),
        λ (x1,x2) (y1,y2) => (E1.Eq_D x1 y1,E2.Eq_D x2 y2),
        λ n => (E1.Var_D n,E2.Var_D n),
        λ (x1,x2) (y1,y2) => (E1.Appx_D x1 y1,E2.Appx_D x2 y2),
        λ (x1,x2) (y1,y2) => (E1.Appi_D x1 y1,E2.Appi_D x2 y2),
        λ (x1,x2) (y1,y2) => (E1.Transp_D x1 y1,E2.Transp_D x2 y2)
      ⟩
    def elimProduct (E1 E2 : eliminator) : eliminator := ⟨
      elimProduct_inner E1.toeliminator_inner E2.toeliminator_inner,
      E1.Output × E2.Output,
      λ (x1,x2) topnames telescopes => (E1.mkOutput x1 topnames telescopes, E2.mkOutput x2 topnames telescopes)
    ⟩
    def elimProduct' (E1 E2 : eliminator) (Output' : Type) (mkOutput' : E1.Con_D → E2.Con_D → List String → List (List ArgMarker) → Output'): eliminator := ⟨
      elimProduct_inner E1.toeliminator_inner E2.toeliminator_inner,
      Output',
      λ (x1,x2) => mkOutput' x1 x2
    ⟩
    def elimProductMany : List (Sigma (λ elim_inner => eliminator_outer elim_inner × List (eliminator_outer elim_inner))) → eliminator
    | [] => dummy -- avoid this
    | [⟨_,eo1,eos⟩] => toEliminator $ List.foldl elimProduct_outer eo1 eos
    | ⟨_,eo1,eos⟩::rest => elimProduct (toEliminator $ List.foldl elimProduct_outer eo1 eos) (elimProductMany rest)

    def elim_post (Elim : eliminator) {Output' : Type} (f : Elim.Output → Output') : eliminator :=
      ⟨ Elim.toeliminator_inner, Output',
        λ Γ topnames telescopes => f (Elim.mkOutput Γ topnames telescopes)⟩



    def litToInner : Expr → Expr := .app (.const ``eliminator.toeliminator_inner [])
    def litEmpty_D : Expr → Expr := .app (.const ``eliminator_inner.Empty_D []) ∘ litToInner
    def litExtend_D : Expr → Expr := .app (.const ``eliminator_inner.Extend_D []) ∘ litToInner
    def litUU_D : Expr → Expr := .app (.const ``eliminator_inner.UU_D []) ∘ litToInner
    def litEl_D : Expr → Expr := .app (.const ``eliminator_inner.El_D []) ∘ litToInner
    def litPix_D : Expr → Expr := .app (.const ``eliminator_inner.Pix_D []) ∘ litToInner
    def litPii_D : Expr → Expr := .app (.const ``eliminator_inner.Pii_D []) ∘ litToInner
    def litEq_D : Expr → Expr := .app (.const ``eliminator_inner.Eq_D []) ∘ litToInner
    def litAppx_D : Expr → Expr := .app (.const ``eliminator_inner.Appx_D []) ∘ litToInner
    def litAppi_D : Expr → Expr := .app (.const ``eliminator_inner.Appi_D []) ∘ litToInner
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
          .app (.const ``eliminator_inner.Pix_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Pii_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Eq_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Var_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Appx_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
          .app (.const ``eliminator_inner.Appi_D []) (.app (.const ``eliminator.toeliminator_inner []) litElim),
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
          let mRes ← metaTyApp argInstr.firstExpl mt1 mA1 mt2 mA2
          return (mkAppN (litAppx_D Elim) #[t1,t2], metaAPP mt1 mt2,mRes)
    | `(gat_tm| $g1:gat_tm { $g2:gat_tm } ) => do
          let (t1,mt1,mA1) ← elabGATTm Elim g1
          let (t2,mt2,mA2) ← elabGATTm Elim g2
          let mRes ← metaTyApp argInstr.firstImpl mt1 mA1 mt2 mA2
          return (mkAppN (litAppi_D Elim) #[t1,t2], metaAPP mt1 mt2,mRes)
    | `(gat_tm| $i:ident ) => do
          let (mb,m,b) ← varTelLkup i.getId.toString
          return (mkAppN (litVar_D Elim) #[mkNatLit b],mb,m)
    | `(gat_tm| $g1 #⟨ $g2 ⟩ ) => do
          let (t1,mt1,mX1) ← elabGATTm Elim g1
          let (t2,mt2,mX2) ← elabGATTm Elim g2
          let mresT ← failIfBadTransp mt2 mt1 mX2 mX1
          return (mkAppN (litTransp_D Elim) #[t2,t1],metaTRANSP mt2 mt1,mresT)
    | _ => throwError "TmFail"

    instance  : Inhabited (Syntax → StateT st MetaM (Expr × metaTyMarker)) where
      default _ := pure (.const ``true [],metaUU)

    partial def elabGATTy (Elim : Expr) : Syntax → StateT st MetaM (Expr × metaTyMarker)
    | `(gat_ty| U ) => do
        return (litUU_D Elim,metaUU)
    | `(gat_ty| $x:gat_tm ) => do
        let (t,mt,mX) ← elabGATTm Elim x
        failIfNotU "Bad El" mt mX
        return (mkAppN (litEl_D Elim) #[t],metaEl mt)
    | `(gat_ty| $t1:gat_tm ≡ $t2:gat_tm) => do
        let (tt1,mt1,mX1) ← elabGATTm Elim t1
        let (tt2,mt2,mX2) ← elabGATTm Elim t2
        let mX ← failIfBadEq mt1 mt2 mX1 mX2
        return (mkAppN (litEq_D Elim) #[tt1,tt2],metaEq mX mt1 mt2)
    | `(gat_ty| $T:gat_tm ⇒ $T':gat_ty) => do
        let (domain,mt,mX) ← elabGATTm Elim T
        failIfNotU "Failed to create argument" mt mX
        extendTel (Anon,mt)
        let (codomain,finalT) ← elabGATTy Elim T'
        return (mkAppN (litPix_D Elim) #[domain,codomain],finalT)
    | `(gat_ty| ( $is:ident* : $T:gat_tm ) ⇒ $T':gat_ty) => do
        Array.foldr (λ i getCodomain => do
          let (domain,mt,mX) ← elabGATTm Elim T
          failIfNotU "Failed to create argument" mt mX
          extendTel (Expl i.getId.toString, mt)
          let (codomain,finalT) ← getCodomain
          return (mkAppN (litPix_D Elim) #[domain,codomain],finalT)
        ) (elabGATTy Elim T') is
    | `(gat_ty| { $is:ident* : $T:gat_tm } ⇒ $T':gat_ty) => do
        Array.foldr (λ i getCodomain => do
          let (domain,mt,mX) ← elabGATTm Elim T
          failIfNotU "Failed to create argument" mt mX
          extendTel (Impl i.getId.toString, mt)
          let (codomain,finalT) ← getCodomain
          return (mkAppN (litPii_D Elim) #[domain,codomain],finalT)
        ) (elabGATTy Elim T') is
    | `(gat_ty| ( $is:gat_underscore* : $T:gat_tm ) ⇒ $T':gat_ty) => do
        Array.foldr (λ _ getCodomain => do
          let (domain,mt,mX) ← elabGATTm Elim T
          failIfNotU "Failed to create argument" mt mX
          extendTel (Anon, mt)
          let (codomain,finalT) ← getCodomain
          return (mkAppN (litPix_D Elim) #[domain,codomain],finalT)
        ) (elabGATTy Elim T') is
    | _ => throwError "TyFail"

    def elabGATdecl (Elim : Expr) (getRest : StateT st MetaM Expr) : Syntax → StateT st MetaM Expr
    | `(gat_decl|  $is:ident* : $g:gat_ty ) => do
        Array.foldl (λ getRest' i => do
          let restCon ← getRest'
          setCurrentName i.getId.toString
          let (T,finalT) ← elabGATTy Elim g
          extendMain finalT
          return mkAppN (litExtend_D Elim) #[restCon,T]
        ) getRest is
    | _ => throwError "GATdecl_Fail"

    def AMList := List ArgMarker

    def elabGAT (Elim : Expr) : Syntax → MetaM Expr
    | `(con_inner| $ds:gat_decl,* ) => do
        let (resCon,VV) ← StateT.run (Array.foldl (elabGATdecl Elim) (return litEmpty_D Elim) ds.getElems) (stEmpty false)
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit (List.reverse VV.topnames))
        let telescopes ← List.mapM mkMetaTyLit' (List.reverse VV.telescopes) >>= mkListLit (.const ``AMList [])
        return mkAppN (litMk Elim) #[resCon,topList,telescopes]
    | _ => throwError "GAT_Fail"


  end mainFunctions
end elaborator

namespace basicEliminators

  open preTy preTm
  open nouGATmeta
  open elabState
  open elaborator
  open ArgMarker

    def preElim_inner : eliminator_inner := ⟨
        preCon,
        preTy,
        preTm,
        preEMPTY,
        preEXTEND,
        preUU,
        preEL,
        prePI,
        prePI,
        preEQ,
        preVAR,
        preAPP,
        preAPP,
        preTRANSP⟩

    def GATdataElim_outer : eliminator_outer preElim_inner := ⟨ GATdata, GATdata.mk ⟩
    def GATdataElim : eliminator := toEliminator GATdataElim_outer

    def justGATElim : eliminator := ⟨preElim_inner, preCon, λ Γ _ _ => Γ⟩


    declare_syntax_cat condata_outer
    syntax "[GATdata|" con_inner "]" : condata_outer
    syntax "[justGAT|" con_inner "]" : condata_outer
    syntax "[rawGAT|" con_inner "]" : condata_outer


  section rawGAT
    structure rawGAT where
      (con : preCon)
      (topnames : List String)
      (telescopes : List metaTy)

    def elabGATraw  : Syntax → MetaM Expr
    | `(con_inner| $ds:gat_decl,* ) => do
        let (resCon,VV) ← StateT.run (Array.foldl (elabGATdecl (mkLitElim (.const ``justGATElim []))) (return (.const ``preEMPTY [])) ds.getElems) (stEmpty true)
        let topList ← mkListLit (.const ``String []) (List.map mkStrLit VV.topnames)
        let telescopes ← List.mapM mkMetaTyLit VV.telescopes >>= mkListLit (.const ``metaTy [])
        return mkAppN (.const ``rawGAT.mk []) #[resCon,topList,telescopes]
    | _ => throwError "rawGAT_Fail"
  end rawGAT

  section augGAT
    inductive augTm : Type where
    | augVAR : Nat → augTm
    | augAPPx : augTm → augTm → augTm
    | augAPPi : augTm → augTm → augTm
    | augTRANSP : augTm → augTm → augTm

    inductive augTyMarker' : Type where
    | augUU' : augTyMarker'
    | augEL' : augTm → augTyMarker'
    | augPIx' : augTm → augTyMarker' → augTyMarker'
    | augPIi' : augTm → augTyMarker' → augTyMarker'
    | augEQ' : augTm → augTm → augTyMarker'

    inductive augTyMarker : Type where
    | augUU : augTyMarker
    | augEL : augTm → augTyMarker
    | augPI : ArgMarker → augTm → augTyMarker → augTyMarker
    | augEQ : augTm → augTm → augTyMarker

    inductive augTy : Type where
    | mkAugTy : ArgMarker → augTyMarker → augTy

    open augTm augTy augTyMarker augTyMarker'

    def augElim_inner : eliminator_inner := ⟨
        List augTyMarker',
        augTyMarker',
        augTm,
        [],
        λ 𝔊 A => A :: 𝔊,
        augUU',
        augEL',
        augPIx',
        augPIi',
        augEQ',
        augVAR,
        augAPPx,
        augAPPi,
        augTRANSP⟩

    def augCombine_single : augTyMarker' → List ArgMarker → Option augTyMarker
    | augUU', [] => return augUU
    | augEL' X, [] => return augEL X
    | augEQ' t1 t2, [] => return augEQ t1 t2
    | augPIx' X Y, Expl s :: tele => do
        let resY ← augCombine_single Y tele
        return augPI (Expl s) X resY
    | augPIx' X Y, Anon :: tele => do
        let resY ← augCombine_single Y tele
        return augPI Anon X resY
    | augPIi' X Y, Impl s :: tele => do
        let resY ← augCombine_single Y tele
        return augPI (Impl s) X resY
    | _,_ => none

    def augCombine_core : List augTyMarker' → List String → List (List ArgMarker) → Option (List augTy)
    | aT::augRest, s::topnames, tele::telescopes => do
      let firstTy ← augCombine_single aT tele
      let res ← augCombine_core augRest topnames telescopes
      return mkAugTy (Expl s) firstTy :: res
    | [], [], [] => return []
    | _, _, _ => none

    def augCombine (augCon : List augTyMarker') (topnames : List String) (telescopes : List (List ArgMarker)) : List augTy := match augCombine_core augCon (List.reverse topnames) (List.reverse telescopes) with
    | some l => l
    | none => []

    def augElim_outer : eliminator_outer augElim_inner := ⟨ List augTy, augCombine ⟩

    def augElim : eliminator := toEliminator augElim_outer

    def augTm.toString : augTm → String
    -- | augAPPx (augAPPx (augAPPx (augAPPx (augAPPx f t1) t2) t3) t4) t5 => mkParen (augTm.toString f) ++ " @ " ++ mkParen (augTm.toString t1) ++ " @ " ++ mkParen (augTm.toString t2) ++ " @ " ++ mkParen (augTm.toString t3) ++ " @ " ++ mkParen (augTm.toString t4) ++ " @ " ++ mkParen (augTm.toString t5)
    -- | augAPPx (augAPPx (augAPPx (augAPPx f t1) t2) t3) t4 => mkParen (augTm.toString f) ++ " @ " ++ mkParen (augTm.toString t1) ++ " @ " ++ mkParen (augTm.toString t2) ++ " @ " ++ mkParen (augTm.toString t3) ++ " @ " ++ mkParen (augTm.toString t4)
    -- | augAPPx (augAPPx (augAPPx f t1) t2) t3 => mkParen (augTm.toString f) ++ " @ " ++ mkParen (augTm.toString t1) ++ " @ " ++ mkParen (augTm.toString t2) ++ " @ " ++ mkParen (augTm.toString t3)
    -- | augAPPx (augAPPx f t1) t2 => mkParen (augTm.toString f) ++ " @ " ++ mkParen (augTm.toString t1) ++ " @ " ++ mkParen (augTm.toString t2)
    | augAPPx f t =>   mkParen (augTm.toString f) ++ " @ " ++ mkParen (augTm.toString t)
    | augAPPi f t =>   mkParen (augTm.toString f) ++ " @ {" ++ augTm.toString t ++ "}"
    | augVAR n => Nat.repr n
    | augTRANSP eq y => "transp " ++ mkParen (augTm.toString eq) ++ " " ++ mkParen (augTm.toString y)

    def augTyMarker.toString : augTyMarker → String
    | augUU => "U"
    | augEL X => X.toString
    | augEQ s t => mkParen s.toString  ++ " = " ++ mkParen t.toString
    | augPI Anon X Y => X.toString ++ " ⇒ " ++ Y.toString
    | augPI (Expl s) X Y => "(" ++ s ++ " : " ++ X.toString ++ ") ⇒ " ++ Y.toString
    | augPI (Impl s) X Y => "{" ++ s ++ " : " ++ X.toString ++ "} ⇒ " ++ Y.toString

    def augTy.toString : augTy → String
    | mkAugTy Anon aT => "_ : " ++ aT.toString
    | mkAugTy (Expl s) aT => "(" ++ s ++ " : " ++ aT.toString ++ ")"
    | mkAugTy (Impl s) aT => "{" ++ s ++ " : " ++ aT.toString ++ "}"

    instance : Repr augTy := ⟨ λ a _ => augTy.toString a ⟩

    syntax "[augcon|" con_inner "]" : condata_outer
  end augGAT

end basicEliminators
