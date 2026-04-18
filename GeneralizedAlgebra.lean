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
  ("Set","𝔖𝔢𝔱",𝔖𝔢𝔱),
  ("P","𝔓",𝔓),
  ("B","𝔅",𝔅),
  ("N","𝔑",𝔑),
  ("EO","𝔈𝔒",𝔈𝔒),
  ("Quiv","𝔔𝔲𝔦𝔳",𝔔𝔲𝔦𝔳),
  ("rQuiv","𝔯𝔔𝔲𝔦𝔳",𝔯𝔔𝔲𝔦𝔳),
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
