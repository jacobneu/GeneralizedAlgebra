-- import GeneralizedAlgebra
import Lake
open Lake DSL

package «generalizedalgebra» where
  -- add package configuration options here

lean_lib «GeneralizedAlgebra» where

@[default_target]
lean_exe «generalizedalgebra» where
  root := `Main
