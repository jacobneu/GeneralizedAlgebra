import GeneralizedAlgebra.nouGAT

open Lean Elab Meta
open preTy preTm
open elaborator


def preElim_inner : eliminator_inner := ⟨
    preCon,
    preTy,
    preTm,
    preEMPTY,
    preEXTEND,
    preUU,
    preEL,
    prePI,
    preEQ,
    preVAR,
    preAPP,
    preTRANSP⟩

def GATdataElim : eliminator := ⟨ preElim_inner, GATdata, GATdata.mk ⟩
def justGATElim : eliminator := ⟨preElim_inner, preCon, λ Γ _ _ => Γ⟩

declare_syntax_cat condata_outer
syntax "[GATdata|" "]" : condata_outer
syntax "[GATdata|" con_inner "]" : condata_outer
syntax "[justGAT|" "]" : condata_outer
syntax "[justGAT|" con_inner "]" : condata_outer

-- syntax "[rawGAT|" con_inner "]" : condata_outer
    -- declare_syntax_cat con_outer
    -- syntax "⦃" "⦄" : con_outer
    -- syntax "⦃" con_inner "⦄" : con_outer

def elabGATCon : Syntax → MetaM Expr
| `(condata_outer| [GATdata| ] ) =>
    elabEmptyGAT (mkLitElim (.const ``GATdataElim []))
| `(condata_outer| [GATdata| $s:con_inner ] ) =>
    elabNonemptyGAT (mkLitElim (.const ``GATdataElim [])) s
| `(condata_outer| [justGAT| ] ) =>
    elabEmptyGAT (mkLitElim (.const ``justGATElim []))
| `(condata_outer| [justGAT| $s:con_inner ] ) =>
    elabNonemptyGAT (mkLitElim (.const ``justGATElim [])) s
| _ => throwError "Syntax fail"


elab g:condata_outer : term => elabGATCon g
