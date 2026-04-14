import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.SectString
import GeneralizedAlgebra.eliminate.HomString

open Lean Elab Meta
open preTy preTm
open elaborator
open basicEliminators




syntax "⦃" con_inner "⦄" : condata_outer


structure GAT where
    (con : preCon)
    (topnames : List String)
    (telescopes : List (List ArgMarker))
    (augcon : List augTy)
    (algStr : List String)
    (dalgStr : List String)
    (homStr : List String)
    (sectStr : List String)

def fullElim : eliminator :=
    elim_post (
        elimProductMany [
            ⟨_,GATdataElim_outer,[]⟩,
            ⟨_,augElim_outer,[]⟩
        ]
        )
    (λ (⟨Γ,topnames,telescopes⟩,augcon) =>
        GAT.mk Γ topnames telescopes augcon (AlgStr_Con augcon) (DAlgStr_Con augcon) (HomStr_Con augcon) (SectStr_Con augcon)
        )

def elabGATCon : Syntax → MetaM Expr
| `(condata_outer| [GATdata| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``GATdataElim [])) s

| `(condata_outer| [justGAT| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``justGATElim [])) s

| `(condata_outer| [augcon| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``augElim [])) s

| `(condata_outer| [rawGAT| $s:con_inner ] ) =>
    elabGATraw s

| `(condata_outer| [AlgStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``AlgStrElim [])) s

| `(condata_outer| [DAlgStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``DAlgStrElim [])) s

| `(condata_outer| [HomStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``HomStrElim [])) s

| `(condata_outer| [SectStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``SectStrElim [])) s

| `(condata_outer| ⦃ $s:con_inner ⦄ ) =>
    elabGAT (mkLitElim (.const ``fullElim [])) s
| _ => throwError "Syntax fail"


elab g:condata_outer : term => elabGATCon g
