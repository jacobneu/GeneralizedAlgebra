import GeneralizedAlgebra

def main : List String → IO PUnit
| theCmdStr::theGATstr::reps => do
    let (frakStr,theGAT) := match (List.find? (λ (gs,_,_) => gs == theGATstr) GATlist) with
      | some (_,𝔊s,𝔊) => (𝔊s,𝔊)
      | _ => ("𝔖𝔢𝔱",𝔖𝔢𝔱)
    let theCmd := match theCmdStr with
      | "Con" => λ G (𝔊 : GAT) =>
          List.forM  ([G ++ " = ◇"] ++ List.map (" ▷ " ++ preTyrepr ·) (List.reverse 𝔊.con)) IO.println
      | "augcon" => λ G 𝔊 =>
          List.forM  ([G ++ " = ◇"] ++ List.map (" ▷ " ++ basicEliminators.augTyrepr ·) (List.reverse 𝔊.augcon)) IO.println
      | "Alg" => λ G 𝔊 =>
          List.forM (["record " ++ G ++ "-Alg where "] ++ List.map ("    " ++ mkReplace reps ·) 𝔊.algStr) IO.println
      | "DAlg" => λ G 𝔊 =>
          List.forM (["record " ++ G ++ "-DAlg (" ++ (String.intercalate "," 𝔊.topnames) ++ ") where"] ++ List.map ("    " ++  mkReplace reps ·) 𝔊.dalgStr) IO.println
      | "Hom" => λ G 𝔊 =>
          List.forM (["record " ++ G ++ "-Hom (" ++ (String.intercalate "," (List.map zeroFn 𝔊.topnames)) ++ ") (" ++ (String.intercalate "," (List.map oneFn 𝔊.topnames)) ++ ") where"] ++ List.map ("    " ++  mkReplace reps ·) 𝔊.homStr) IO.println
      | _ => λ _ _ => IO.println "Error: unknown command"
    theCmd frakStr theGAT
| _ => IO.println "Error: command and GAT not supplied"
