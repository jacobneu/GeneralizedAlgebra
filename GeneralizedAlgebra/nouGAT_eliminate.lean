import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.SectString
import GeneralizedAlgebra.eliminate.HomString
import GeneralizedAlgebra.eliminate.formats.PseudoAgda

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

def GAT.algStr_on (𝔊 : GAT) (ss : List String) :=
    AlgStr_Con pseudoAgda 𝔊.augcon ss
def GAT.dalgStr_on (𝔊 : GAT) (ss : List String) :=
    DAlgStr_Con pseudoAgda 𝔊.augcon ss
def GAT.sectStr_on (𝔊 : GAT) (ss : List String) :=
    SectStr_Con pseudoAgda 𝔊.augcon ss


def fullElim : eliminator :=
    elim_post (
        elimProductMany [
            ⟨_,GATdataElim_outer,[]⟩,
            ⟨_,augElim_outer,[]⟩
        ]
        )
    (λ (⟨Γ,topnames,telescopes⟩,augcon) =>
        GAT.mk Γ topnames telescopes augcon (AlgStr_Con pseudoAgda augcon) (DAlgStr_Con pseudoAgda augcon) (HomStr_Con pseudoAgda augcon) (SectStr_Con pseudoAgda augcon)
        )

def psAlgStrElim := AlgStrElim pseudoAgda
def psDAlgStrElim := DAlgStrElim pseudoAgda
def psHomStrElim := HomStrElim pseudoAgda
def psSectStrElim := SectStrElim pseudoAgda

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
    elabGAT (mkLitElim (.const ``psAlgStrElim [])) s

| `(condata_outer| [DAlgStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``psDAlgStrElim [])) s

| `(condata_outer| [HomStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``psHomStrElim [])) s

| `(condata_outer| [SectStr| $s:con_inner ] ) =>
    elabGAT (mkLitElim (.const ``psSectStrElim [])) s

| `(condata_outer| ⦃ $s:con_inner ⦄ ) =>
    elabGAT (mkLitElim (.const ``fullElim [])) s
| _ => throwError "Syntax fail"


elab g:condata_outer : term => elabGATCon g
