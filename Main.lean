import GeneralizedAlgebra

def main : List String → IO PUnit
| theCmdStr::theGATstr::_ => do
    let (frakStr,theGAT) := match (List.find? (λ (gs,_,_) => gs == theGATstr) GATlist) with
      | some (_,𝔊s,𝔊) => (𝔊s,𝔊)
      | _ => ("𝔖𝔢𝔱",𝔖𝔢𝔱_data)
    let theCmd := match theCmdStr with
      | "Con" => λ G (𝔊 : GATdata) =>
          List.forM  ([G ++ " = ◇"] ++ List.map (λ T => " ▷ " ++ preTyrepr T) (𝔊.con)) IO.println
      | "Alg" => printAlg
      | "DAlg" => printDAlg
      | _ => printAlg
    theCmd frakStr theGAT
| _ => IO.println "Error: command and GAT not supplied"
