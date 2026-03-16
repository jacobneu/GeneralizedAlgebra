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
import GeneralizedAlgebra.signatures.PCwF
import GeneralizedAlgebra.signatures.GAT_CwF


def GATlist := [
  ("Set","𝔖𝔢𝔱",𝔖𝔢𝔱_data),
  ("P","𝔓",𝔓_data),
  ("B","𝔅",𝔅_data),
  ("N","𝔑",𝔑_data),
  ("EO","𝔈𝔒",𝔈𝔒_data),
  ("Quiv","𝔔𝔲𝔦𝔳",𝔔𝔲𝔦𝔳_data),
  ("rQuiv","𝔯𝔔𝔲𝔦𝔳",𝔯𝔔𝔲𝔦𝔳_data),
  ("Mon","𝔐𝔬𝔫",𝔐𝔬𝔫_data),
  ("Grp","𝔊𝔯𝔭",𝔊𝔯𝔭_data),
  ("PreOrd","𝔓𝔯𝔢𝔒𝔯𝔡",𝔓𝔯𝔢𝔒𝔯𝔡_data),
  ("Setoid","𝔖𝔢𝔱𝔬𝔦𝔡",𝔖𝔢𝔱𝔬𝔦𝔡_data),
  ("Cat","ℭ𝔞𝔱",ℭ𝔞𝔱_data),
  ("Grpd","𝔊𝔯𝔭𝔡",𝔊𝔯𝔭𝔡_data),
  ("CwF","ℭ𝔴𝔉",ℭ𝔴𝔉_data),
  ("PCwF","𝔓ℭ𝔴𝔉",𝔓ℭ𝔴𝔉_data),
  ("GATCwF","𝔊𝔄𝔗ℭ𝔴𝔉",𝔊𝔄𝔗ℭ𝔴𝔉_data)]

-- Functions for displaying
def printIndent s := IO.println ("    " ++ s)

def printAlg (G : String) (𝔊 : GATdata) : IO PUnit := do
  IO.println $ "record " ++ G ++ "-Alg where "
  List.forM (AlgStr_Con 𝔊) printIndent

def printDAlg (G : String) (𝔊 : GATdata) : IO PUnit := do
  IO.println $ "record " ++ G ++ "-DAlg (" ++ (String.intercalate "," (List.reverse 𝔊.topnames)) ++ ") where"
  List.forM (DAlgStr_Con 𝔊) printIndent
