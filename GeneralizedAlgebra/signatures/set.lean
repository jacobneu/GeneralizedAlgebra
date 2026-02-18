import GeneralizedAlgebra.nouGAT

def 𝔖𝔢𝔱_data : GATdata :=
  [GATdata| X : U ]

def 𝔖𝔢𝔱 : GAT := ⟨
  𝔖𝔢𝔱_data,
  by
    apply wellCon.wellCons
    apply wellTy.wellUU
    apply wellCon.wellEmpty
⟩
