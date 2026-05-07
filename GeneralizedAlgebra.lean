import GeneralizedAlgebra.nouGAT_eliminate
-- import GeneralizedAlgebra.eliminate.DAlgString
-- import GeneralizedAlgebra.eliminate.ConPrinting

import GeneralizedAlgebra.signatures.set
import GeneralizedAlgebra.signatures.pointed
import GeneralizedAlgebra.signatures.bipointed
import GeneralizedAlgebra.signatures.nat
import GeneralizedAlgebra.signatures.evenodd
import GeneralizedAlgebra.signatures.quiver
import GeneralizedAlgebra.signatures.refl_quiver
import GeneralizedAlgebra.signatures.dgraph
import GeneralizedAlgebra.signatures.ugraph
import GeneralizedAlgebra.signatures.boolean
import GeneralizedAlgebra.signatures.interior
import GeneralizedAlgebra.signatures.monoid
import GeneralizedAlgebra.signatures.group
import GeneralizedAlgebra.signatures.preorder
import GeneralizedAlgebra.signatures.setoid
import GeneralizedAlgebra.signatures.category
import GeneralizedAlgebra.signatures.groupoid
import GeneralizedAlgebra.signatures.CwF
import GeneralizedAlgebra.signatures.PCwF
import GeneralizedAlgebra.signatures.GAT_CwF


  -- ⟨ℭ𝔴𝔉,"ℭ𝔴𝔉","CwF",none,none,none⟩,
  -- ⟨ℭ𝔴𝔉₁,"ℭ𝔴𝔉₁","CwF+unit",none,none,none⟩,
  -- ⟨ℭ𝔴𝔉₂,"ℭ𝔴𝔉₂","CwF+bool",none,none,none⟩,
  -- ⟨ℭ𝔴𝔉pi,"ℭ𝔴𝔉pi","CwF+Pi",none,none,none⟩,
  -- ⟨𝔓ℭ𝔴𝔉,"𝔓ℭ𝔴𝔉","PCwF",none,none,none⟩


def GATlist := [
  ("Set","𝔖𝔢𝔱",𝔖𝔢𝔱),
  ("P","𝔓",𝔓),
  ("B","𝔅",𝔅),
  ("N","𝔑",𝔑),
  ("EO","𝔈𝔒",𝔈𝔒),
  ("Quiv","𝔔𝔲𝔦𝔳",𝔔𝔲𝔦𝔳),
  ("rQuiv","𝔯𝔔𝔲𝔦𝔳",𝔯𝔔𝔲𝔦𝔳),
  ("dGraph","𝔡𝔊𝔯𝔞𝔭𝔥",𝔡𝔊𝔯𝔞𝔭𝔥),
  ("uGraph","𝔲𝔊𝔯𝔞𝔭𝔥",𝔲𝔊𝔯𝔞𝔭𝔥),
  ("Bool","𝔅𝔬𝔬𝔩",𝔅𝔬𝔬𝔩),
  ("Interior","ℑ𝔫𝔱𝔢𝔯𝔦𝔬𝔯",ℑ𝔫𝔱𝔢𝔯𝔦𝔬𝔯),
  ("Mon","𝔐𝔬𝔫",𝔐𝔬𝔫),
  ("Grp","𝔊𝔯𝔭",𝔊𝔯𝔭),
  ("PreOrd","𝔓𝔯𝔢𝔒𝔯𝔡",𝔓𝔯𝔢𝔒𝔯𝔡),
  ("Setoid","𝔖𝔢𝔱𝔬𝔦𝔡",𝔖𝔢𝔱𝔬𝔦𝔡),
  ("Cat","ℭ𝔞𝔱",ℭ𝔞𝔱),
  ("Grpd","𝔊𝔯𝔭𝔡",𝔊𝔯𝔭𝔡),
  ("CwF","ℭ𝔴𝔉",ℭ𝔴𝔉),
  ("PCwF","𝔓ℭ𝔴𝔉",𝔓ℭ𝔴𝔉),
  -- ("GATCwF","𝔊𝔄𝔗ℭ𝔴𝔉",𝔊𝔄𝔗ℭ𝔴𝔉)
  ]
def mkMain (SF: StringFormat): List String → IO PUnit
| theCmdStr::theGATstr::reps => do
    let (frakStr,theGAT) := match (List.find? (λ (gs,_,_) => gs == theGATstr) GATlist) with
      | some (_,𝔊s,𝔊) => (𝔊s,𝔊)
      | _ => ("𝔖𝔢𝔱",𝔖𝔢𝔱)
    let deco : Option sfDecor := match theCmdStr with
      | "Con" => some sfDecor.sfId
      | "Alg" => some sfDecor.sfAlg
      | "DAlg" => some sfDecor.sfDalg
      | "Hom" => some sfDecor.sfHom
      | "Sect" => some sfDecor.sfSect
      | _ => none
    match deco with
      | none => IO.println "Error: unknown command"
      | some dec => do
          let headings := SF.formatWrapping theGATstr frakStr theGAT.topnames dec
          List.forM (headings.1 ++ List.map (mkReplaceVF reps) (getStr theGAT SF dec) ++ headings.2) IO.println
| _ => IO.println "Error: command and GAT not supplied"
