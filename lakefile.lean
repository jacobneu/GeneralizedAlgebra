import Lake
open Lake DSL

package «GeneralizedAlgebra» where
  -- add package configuration options here

lean_lib «GeneralizedAlgebra» where
  -- add library configuration options here

@[default_target]
lean_exe «generalizedalgebra» where
  root := `Main
