-- import GeneralizedAlgebra
import Lake
open Lake DSL

package «generalizedalgebra» where
  -- add package configuration options here

lean_lib «GeneralizedAlgebra» where

@[default_target]
lean_exe «pseudoAgda» where
  root := `pseudoAgda

@[default_target]
lean_exe «forester» where
  root := `Forester
