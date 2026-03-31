import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.AlgString

open Lean Elab Meta
open preTy preTm
open elaborator
open basicEliminators




syntax "⦃" con_inner "⦄" : condata_outer


structure GAT where
    (con : preCon)
    (topnames : List String)
    (telescopes : List (List (Option String)))
    (algStr : List String)

def fullElim : eliminator :=
    elimProduct_post
        (toEliminator $ List.foldl elimProduct_outer GATdataElim_outer [
            AlgStrElim_outer
        ])
    (λ (⟨Γ,topnames,telescopes⟩,algStrList) =>
        GAT.mk Γ topnames telescopes algStrList)

def elabGATCon : Syntax → MetaM Expr
| `(condata_outer| [GATdata| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``GATdataElim [])) s

| `(condata_outer| [justGAT| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``justGATElim [])) s

| `(condata_outer| [AlgStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``AlgStrElim [])) s

| `(condata_outer| ⦃ $s:con_inner ⦄ ) =>
    elabGAT (mkLitElim (.const ``fullElim [])) s
| _ => throwError "Syntax fail"


elab g:condata_outer : term => elabGATCon g
