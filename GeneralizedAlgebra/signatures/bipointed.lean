import GeneralizedAlgebra.signatures.pointed

def 𝔅_data : GATdata :=
  [GATdata| X : U, x : X, x' : X ]

def 𝔅 : GAT := ⟨
  𝔅_data,
  by
    apply wellCon.wellCons
    apply wellTy.wellEL
    apply @wellTm.wellWkTm _ preTy.preUU
    apply wellTm.wellZero
    apply wellTy.wellUU
    exact 𝔓.2
⟩
