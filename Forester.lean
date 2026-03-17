import GeneralizedAlgebra
import GeneralizedAlgebra.eliminate.DAlgForester


def main : List String → IO PUnit
| theCmdStr::theGATstr::_ => do
    let theGAT := match (List.find? (λ (gs,_) => gs == theGATstr) GATlist) with
      | some (_,_,𝔊) => 𝔊
      | _ => 𝔖𝔢𝔱_data
    let theCmd := match theCmdStr with
      | "Con" => ConForester
      | "DAlg" => DAlgForester
      | _ => AlgForester
    List.forM (theCmd theGAT theGATstr) IO.println
| _ => IO.println "Error: command and GAT not supplied"
