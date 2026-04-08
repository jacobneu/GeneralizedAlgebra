import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.HomString

open Lean Elab Meta
open preTy preTm
open elaborator
open basicEliminators




syntax "⦃" con_inner "⦄" : condata_outer


structure GAT where
    (con : preCon)
    (topnames : List String)
    (telescopes : List (List (Option (String × Bool))))
    (augcon : List augTy)
    (algStr : List String)
    (dalgStr : List String)
    (homStr : List String)

def fullElim : eliminator :=
    elim_post (
        elimProductMany [
            ⟨_,GATdataElim_outer,[]⟩,
            ⟨_,augElim_outer,[AlgStrElim_outer,DAlgStrElim_outer,HomStrElim_outer]⟩
        ]
        )
    (λ (⟨Γ,topnames,telescopes⟩,⟨⟨augcon,algstr⟩,dalgstr⟩,homstr) =>
        GAT.mk Γ topnames telescopes augcon algstr dalgstr homstr
        )

def elabGATCon : Syntax → MetaM Expr
| `(condata_outer| [GATdata| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``GATdataElim [])) s

| `(condata_outer| [justGAT| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``justGATElim [])) s

| `(condata_outer| [rawGAT| $s:con_inner ] ) =>
    elabGATraw s

| `(condata_outer| [AlgStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``AlgStrElim [])) s

| `(condata_outer| [DAlgStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``DAlgStrElim [])) s

| `(condata_outer| [HomStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``HomStrElim [])) s

| `(condata_outer| ⦃ $s:con_inner ⦄ ) =>
    elabGAT (mkLitElim (.const ``fullElim [])) s
| _ => throwError "Syntax fail"


elab g:condata_outer : term => elabGATCon g
