import GeneralizedAlgebra.nouGAT
import GeneralizedAlgebra.eliminate.DAlgString
import GeneralizedAlgebra.eliminate.ConPrinting

import GeneralizedAlgebra.signatures.set
import GeneralizedAlgebra.signatures.pointed
import GeneralizedAlgebra.signatures.bipointed
import GeneralizedAlgebra.signatures.nat
import GeneralizedAlgebra.signatures.evenodd
import GeneralizedAlgebra.signatures.quiver
import GeneralizedAlgebra.signatures.refl_quiver
import GeneralizedAlgebra.signatures.monoid
import GeneralizedAlgebra.signatures.group
import GeneralizedAlgebra.signatures.preorder
import GeneralizedAlgebra.signatures.setoid
import GeneralizedAlgebra.signatures.category
import GeneralizedAlgebra.signatures.groupoid
import GeneralizedAlgebra.signatures.CwF
import GeneralizedAlgebra.signatures.GAT_CwF

-- Functions for displaying
def printIndent s := IO.println ("    " ++ s)

def printAlg (G : String) (𝔊 : GATdata) : IO PUnit := do
  IO.println $ "record " ++ G ++ "-Alg where "
  List.forM (AlgStr_Con 𝔊) printIndent

def printDAlg (G : String) (𝔊 : GATdata) : IO PUnit := do
  IO.println $ "record " ++ G ++ "-DAlg (" ++ (String.intercalate "," (List.reverse 𝔊.topnames)) ++ ") where"
  List.forM (DAlgStr_Con 𝔊) printIndent
