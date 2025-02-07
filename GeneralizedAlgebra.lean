import GeneralizedAlgebra.AlgPrinting
import GeneralizedAlgebra.ConPrinting

import GeneralizedAlgebra.signatures.nat
import GeneralizedAlgebra.signatures.quiver
import GeneralizedAlgebra.signatures.refl_quiver
import GeneralizedAlgebra.signatures.monoid
import GeneralizedAlgebra.signatures.preorder
import GeneralizedAlgebra.signatures.setoid
import GeneralizedAlgebra.signatures.category
import GeneralizedAlgebra.signatures.groupoid
import GeneralizedAlgebra.signatures.CwF
import GeneralizedAlgebra.signatures.PCwF

-- Natural numbers
#eval Con_toString 𝔑
#eval Alg 𝔑 Nat_names
#eval DAlg 𝔑 Nat_names ["P","n"]
#eval DAlg 𝔑 Nat_names ["P","base_case","n","ind_step"] true

-- Quivers
#eval Con_toString 𝔔𝔲𝔦𝔳
#eval Alg 𝔔𝔲𝔦𝔳 Quiv_names
-- #eval DAlg 𝔔𝔲𝔦𝔳 Quiv_names

-- Reflexive quivers
#eval Con_toString 𝔯𝔔𝔲𝔦𝔳
#eval Alg 𝔯𝔔𝔲𝔦𝔳 rQuiv_names
-- #eval DAlg 𝔯𝔔𝔲𝔦𝔳 rQuiv_names

-- Monoids
#eval Con_toString 𝔐𝔬𝔫
#eval Alg 𝔐𝔬𝔫 Mon_names true
-- #eval DAlg 𝔯𝔔𝔲𝔦𝔳 rQuiv_names

-- Preorders
#eval Con_toString 𝔓𝔯𝔢𝔒𝔯𝔡
#eval Alg 𝔓𝔯𝔢𝔒𝔯𝔡 PreOrd_names true
-- #eval DAlg 𝔓𝔯𝔢𝔒𝔯𝔡 PreOrd_names

-- Setoids
#eval Con_toString 𝔖𝔢𝔱𝔬𝔦𝔡
#eval Alg 𝔖𝔢𝔱𝔬𝔦𝔡 Setoid_names true
-- #eval DAlg 𝔖𝔢𝔱𝔬𝔦𝔡 Setoid_names

-- Categories
#eval Con_toString ℭ𝔞𝔱
#eval Alg ℭ𝔞𝔱 Cat_names true
-- #eval DAlg ℭ𝔞𝔱 Cat_names

-- Groupoids
#eval Con_toString 𝔊𝔯𝔭𝔡
#eval Alg 𝔊𝔯𝔭𝔡 Grpd_names true
-- #eval DAlg 𝔊𝔯𝔭𝔡 Grpd_names

-- Categories with Families
#eval Con_toString ℭ𝔴𝔉
#eval Alg ℭ𝔴𝔉 CwF_names true
#eval Alg ℭ𝔴𝔉 CwF_inlinenames
-- #eval DAlg ℭ𝔴𝔉 CwF_names

-- Polarized Categories with Families
#eval Con_toString 𝔓ℭ𝔴𝔉
#eval Alg 𝔓ℭ𝔴𝔉 PCwF_names true
-- #eval DAlg 𝔓ℭ𝔴𝔉 PCwF_names
