import GeneralizedAlgebra.signature

open Nat
open Con Subst Ty Tm


mutual
inductive Argument : Type where
|  NonDep : List Token → Argument
|  Dep : List Token → Argument
inductive Token : Type where
| printArg : Nat → Token
| printVarName : Nat → Token
| printStr : String → Token
| printConstrSplit : Token
| printArrow : Token
| BREAK : Token
end
open Argument Token

def newVar ( ty : List Token) : StateT (List Argument) Option Nat := do
  let vars ← get
  let new := NonDep ty
  set $ vars++[new]
  pure $ List.length vars

def countDepends : List Argument → Nat
| [] => 0
| (Dep _)::rest => 1 + countDepends rest
| (NonDep _)::rest => countDepends rest

def getDepends : List Argument → Nat → Option (Bool × Nat × List Token)
| [] , _ => none
| (Dep ts)::_, 0 => return (true,0,ts)
| (NonDep ts)::_, 0 => return (false,0,ts)
| (Dep _)::rest, succ n => do
    let (bit,res,ts) ← getDepends rest n
    return (bit,succ res,ts)
| (NonDep _)::rest, succ n => getDepends rest n

def foldTokens_core (constrSplit : String) (varNames : List String) : Nat → List Argument → List Token → Option String
| succ FUEL, args, printArrow::rest => do
    let restStr ← foldTokens_core constrSplit varNames FUEL args rest
    return (" → " ++ restStr)
| succ FUEL, args, printConstrSplit::rest => do
    let restStr ← foldTokens_core constrSplit varNames FUEL args rest
    return (constrSplit ++ restStr)
| succ FUEL, args, (printStr s)::rest => do
    let restStr ← foldTokens_core constrSplit varNames FUEL args rest
    return (s ++ restStr)
| succ FUEL, args, (printArg n)::rest => do
    let (doPrint, index, ts) ← getDepends args n
    let printRest ← foldTokens_core constrSplit varNames FUEL args rest
    let argType ← foldTokens_core constrSplit varNames FUEL args ts
    let varName ← nth index varNames
    if doPrint
    then return ("(" ++ varName ++ " : " ++ argType ++ ")" ++ printRest)
    else return (argType ++ printRest)
| succ FUEL, args, (printVarName n)::rest => do
    let (_, index, _) ← getDepends args n
    let printRest ← foldTokens_core constrSplit varNames FUEL args rest
    let varName ← nth index varNames
    return (varName ++ printRest)
| _,_,[] => some ""
| _,_, _ => none

def foldTokens (constrSplit : String := " × ") (varNames : List String) (args : List Argument):=
  foldTokens_core constrSplit varNames 1000 args

def genVarNames_core (REPR : Nat → String) (varLetter : String) : Nat → List String → Nat → List String
| 0, varNames,_ => varNames
| succ n, varNames,index => genVarNames_core REPR varLetter n (varNames ++ [varLetter ++ REPR index]) (succ index)

def genVarNames (n : Nat) (starterNames : List String) (varLetter := "X_"): List String :=
  genVarNames_core (if n < 10 then twoRepr else threeRepr) varLetter (n - List.length starterNames) (List.take n starterNames) 0

def pingNth_core : List Argument → Nat → Option (List Argument)
| [],_ => none
| (NonDep ts)::rest,0 => some ((Dep ts)::rest)
| x::rest,succ n => do
  let res ← pingNth_core rest n
  return (x::res)
| L,_ => some L

def pingNth (n :Nat) : StateT (List Argument) Option Unit := do
  let current ← get
  let new ← StateT.lift $ pingNth_core current n
  set new

mutual
  def Alg_Con : Con → StateT (List Argument) Option (List Nat × List Token)
  | EMPTY => pure $ ([],[printStr "⊤"])
  | EMPTY ▷ UU => do
      let theVar ← newVar [printStr "Set"]
      pure ([theVar],[printArg theVar])
  | Γ ▷ A => do
    let (tel,res) ← Alg_Con Γ
    let As ← Alg_Ty A tel
    let theVar ← newVar As
    pure (tel++[theVar],res ++ [printConstrSplit, printStr "(", printArg theVar, printStr ")"])
  def Alg_Ty : Ty → List Nat → StateT (List Argument) Option (List Token)
  | UU,_ => pure [printStr "Set"]
  | EL X, tel => Alg_Tm X tel
  | PI X Y, tel => do
      let Xs ← Alg_Tm X tel
      let Xvar ← newVar Xs
      let Ys ← Alg_Ty Y (tel++[Xvar])
      pure $ [printArg Xvar, printArrow] ++ Ys
  | EQ t t',tel => do
      let ts ← Alg_Tm t tel
      let t's ← Alg_Tm t' tel
      pure $ ts ++ [printStr " = "] ++ t's

  | _,_ => StateT.lift none
  def Alg_Tm (t : Tm) (tel : List Nat) : StateT (List Argument) Option (List Token) :=
  match t,deBruijn t with
    | _,some n => do
        let glob_n ← StateT.lift (nthBackwards n tel)
        pingNth glob_n
        pure $ [printVarName glob_n]
    | (APP f) [ PAIR (ID _) t ]t,_ => do
        let fs ← Alg_Tm f tel
        let ts ← Alg_Tm t tel
        pure $ fs ++ [printStr " ("] ++ ts ++ [printStr ")"]
    | (TRANSP t _),_ => do Alg_Tm t tel
        -- let es ← Alg_Tm e tel
        -- pure $ [printStr "transp "] ++ es ++ [printStr " "] ++ ts
    | _,_ => none
end

def Alg (Γ : Con) (comp_names : List String := []) (recordName : Option String := none) : Option String := do
  let ((tel,res),vars) ← StateT.run (Alg_Con Γ) ([])
  let vars' ← if recordName.isSome then List.foldlM pingNth_core vars tel else some vars
  let compSep := if recordName.isSome then " \n    " else " × "
  let varNames := genVarNames (List.length vars') comp_names
  let algStr ← foldTokens compSep varNames vars' res
  match recordName with
  | (some name) => return "record " ++ name ++ "-Alg where\n    " ++ algStr
  | none => return algStr

mutual
  def DAlg_Con : List String → Con → StateT (List Argument) Option (List Nat × List Token)
  | _,EMPTY => pure $ ([],[printStr "⊤"])
  | carrier::_,EMPTY ▷ UU => do
      let theVar ← newVar [printStr carrier,printArrow,printStr "Set"]
      pure ([theVar],[printArg theVar])
  | alg_comp::Alg_comp,Γ ▷ A => do
    let (tel,res) ← DAlg_Con Alg_comp Γ
    let As ← DAlg_Ty tel ([printStr alg_comp]::(List.map (λ x => [printStr x]) Alg_comp)) A
    let theVar ← newVar As
    pure (tel++[theVar],res ++ [printConstrSplit, printStr "(", printArg theVar, printStr ")"])
  | _,_ => none
  def DAlg_Ty : List Nat → List (List Token) → Ty → StateT (List Argument) Option (List Token)
  | _,carrier::_,UU => pure $ carrier ++ [printArrow,printStr "Set"]
  | tel,alg_elt::_,EL X => DAlg_Tm tel alg_elt X
  | tel,alg_fn::alg_rest,PI X Y => do
      let Atype ← (deBruijn X >>= λ n => nth n alg_rest) <|> some [printStr "?"]
      let alpha ← newVar Atype
      pingNth alpha
      let Xs ← DAlg_Tm tel [printVarName alpha] X
      let Xvar ← newVar Xs
      let Ys ← DAlg_Ty (tel++[Xvar]) (([printStr "("]++alg_fn++[printStr " ",printVarName alpha,printStr ")"])::alg_rest) Y
      pure $ [printArg alpha, printStr " → ",printArg Xvar, printStr " → "] ++ Ys
  -- | EQ t t',tel => do
  --     let ts ← DAlg_Tm t tel
  --     let t's ← DAlg_Tm t' tel
  --     pure $ ts ++ [printStr " = "] ++ t's

  | _,_,_ => StateT.lift none
  def DAlg_Tm (tel : List Nat) (alg_elt : List Token) (t : Tm) : StateT (List Argument) Option (List Token) :=
  match t,deBruijn t with
    | _,some n => do
        let glob_n ← StateT.lift (nthBackwards n tel)
        pingNth glob_n
        pure $ [printVarName glob_n,printStr " "]++alg_elt
  --   | (APP f) [ PAIR (ID _) t ]t,_ => do
  --       let fs ← DAlg_Tm f tel
  --       let ts ← DAlg_Tm t tel
  --       pure $ fs ++ [printStr " "] ++ ts
    | _,_ => none
end

def DAlg (Γ : Con) (Alg_comp_names : List String := []) (comp_names : List String := []) (recordName : Option String := none) : Option String := do
  let Alg_comp := genVarNames (len Γ) Alg_comp_names "Y_"
  let ((tel,res),vars) ← StateT.run (DAlg_Con (List.reverse Alg_comp) Γ) ([])
  let vars' ← if recordName.isSome then List.foldlM pingNth_core vars tel else some vars
  let compSep := if recordName.isSome then "\n    " else " × "
  let varNames := genVarNames (List.length vars') comp_names
  let algStr ← foldTokens compSep varNames vars' res
  match recordName with
  | (some name) => return "record " ++ name ++ "-DAlg " ++ collapse Alg_comp ++ " where\n    " ++ algStr
  | none => return algStr
