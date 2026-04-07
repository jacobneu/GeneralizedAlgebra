import GeneralizedAlgebra

def main : List String → IO PUnit
| theCmdStr::theGATstr::_ => do
    let (frakStr,theGAT) := match (List.find? (λ (gs,_,_) => gs == theGATstr) GATlist) with
      | some (_,𝔊s,𝔊) => (𝔊s,𝔊)
      | _ => ("𝔖𝔢𝔱",𝔖𝔢𝔱)
    let theCmd := match theCmdStr with
      | "Con" => λ G (𝔊 : GAT) =>
          List.forM  ([G ++ " = ◇"] ++ List.map (" ▷ " ++ preTyrepr ·) (List.reverse 𝔊.con)) IO.println
      | "Alg" => λ G 𝔊 =>
          List.forM (["record " ++ G ++ "-Alg where "] ++ List.map ("    " ++ ·) 𝔊.algStr) IO.println
      -- | "DAlg" => printDAlg
      | _ => λ _ _ => IO.println "Error: unknown command"
    theCmd frakStr theGAT
| _ => IO.println "Error: command and GAT not supplied"
