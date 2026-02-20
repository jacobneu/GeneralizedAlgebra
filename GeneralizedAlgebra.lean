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

/-
## Basic structures
-/
-- Sets
#eval 𝔖𝔢𝔱
#eval printAlg "𝔖𝔢𝔱" 𝔖𝔢𝔱_data
#eval printDAlg "𝔖𝔢𝔱" 𝔖𝔢𝔱_data

-- -- Pointed sets
#eval 𝔓
#eval printAlg "𝔓" 𝔓_data
#eval printDAlg "𝔓" 𝔓_data

-- -- Bipointed sets
#eval 𝔅
#eval printAlg "𝔅" 𝔓_data
#eval printDAlg "𝔅" 𝔓_data

-- -- Natural numbers
#eval 𝔑
#eval printAlg "𝔑" 𝔑_data
#eval printDAlg "𝔑" 𝔑_data

-- Even/Odd Natural Numbers
#eval 𝔈𝔒
#eval printAlg "𝔈𝔒" 𝔈𝔒_data
#eval printDAlg "𝔈𝔒" 𝔈𝔒_data

-- Monoids
#eval 𝔐𝔬𝔫
#eval printAlg "𝔐𝔬𝔫" 𝔐𝔬𝔫_data
#eval printDAlg "𝔐𝔬𝔫" 𝔐𝔬𝔫_data

-- Groups
#eval 𝔊𝔯𝔭_data
#eval printAlg "𝔊𝔯𝔭" 𝔊𝔯𝔭_data
#eval printDAlg "𝔊𝔯𝔭" 𝔊𝔯𝔭_data

/-
## Quiver-like structures
-/
-- Quivers
#eval 𝔔𝔲𝔦𝔳
#eval printAlg "𝔔𝔲𝔦𝔳" 𝔔𝔲𝔦𝔳_data
#eval printDAlg "𝔔𝔲𝔦𝔳" 𝔔𝔲𝔦𝔳_data

-- Reflexive quivers
#eval 𝔯𝔔𝔲𝔦𝔳
#eval printAlg "𝔯𝔔𝔲𝔦𝔳" 𝔯𝔔𝔲𝔦𝔳_data
#eval printDAlg "𝔯𝔔𝔲𝔦𝔳" 𝔯𝔔𝔲𝔦𝔳_data

-- Preorders
#eval 𝔓𝔯𝔢𝔒𝔯𝔡_data
#eval printAlg "𝔓𝔯𝔢𝔒𝔯𝔡" 𝔓𝔯𝔢𝔒𝔯𝔡_data
#eval printDAlg "𝔓𝔯𝔢𝔒𝔯𝔡" 𝔓𝔯𝔢𝔒𝔯𝔡_data

-- Setoids
#eval 𝔖𝔢𝔱𝔬𝔦𝔡_data
#eval printAlg "𝔖𝔢𝔱𝔬𝔦𝔡" 𝔖𝔢𝔱𝔬𝔦𝔡_data
#eval printDAlg "𝔖𝔢𝔱𝔬𝔦𝔡" 𝔖𝔢𝔱𝔬𝔦𝔡_data

-- Categories
#eval ℭ𝔞𝔱_data
#eval printAlg "ℭ𝔞𝔱" ℭ𝔞𝔱_data
#eval printDAlg "ℭ𝔞𝔱" ℭ𝔞𝔱_data

-- Groupoids
#eval 𝔊𝔯𝔭𝔡_data
#eval printAlg "𝔊𝔯𝔭𝔡" 𝔊𝔯𝔭𝔡_data
#eval printDAlg "𝔊𝔯𝔭𝔡" 𝔊𝔯𝔭𝔡_data


/-
## Models of Type Theory
-/
-- Categories with Families
#eval ℭ𝔴𝔉_data
#eval printAlg "ℭ𝔴𝔉" ℭ𝔴𝔉_data
#eval printDAlg "ℭ𝔴𝔉" ℭ𝔴𝔉_data

-- GAT signature Categories with Families
#eval 𝔊𝔄𝔗ℭ𝔴𝔉_data
#eval printAlg "𝔊𝔄𝔗ℭ𝔴𝔉" 𝔊𝔄𝔗ℭ𝔴𝔉_data
#eval printDAlg "𝔊𝔄𝔗ℭ𝔴𝔉" 𝔊𝔄𝔗ℭ𝔴𝔉_data
