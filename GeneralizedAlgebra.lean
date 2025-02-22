import GeneralizedAlgebra.AlgPrinting
import GeneralizedAlgebra.ConPrinting

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


/-
## Basic structures
-/
-- Sets
#eval Con_toString 𝔖𝔢𝔱
#eval Alg 𝔖𝔢𝔱 Set_names
#eval DAlg 𝔖𝔢𝔱 Set_names ["P"]
#eval DAlg 𝔖𝔢𝔱 Set_names ["P"] (some "𝔖𝔢𝔱")

-- Pointed sets
#eval Con_toString 𝔓
#eval Alg 𝔓 Pointed_names
#eval DAlg 𝔓 Pointed_names ["P"]
#eval DAlg 𝔓 Pointed_names ["P","p₀"] (some "𝔓")

-- Bipointed sets
#eval Con_toString 𝔅
#eval Alg 𝔅 Bipointed_names
#eval DAlg 𝔅 Bipointed_names ["P"]
#eval DAlg 𝔅 Bipointed_names ["P","p₀","p₁"] (some "𝔅")

-- Natural numbers
#eval Con_toString 𝔑
#eval Alg 𝔑 Nat_names
#eval DAlg 𝔑 Nat_names ["P","n"]
#eval DAlg 𝔑 Nat_names ["P","base_case","n","ind_step"] (some "𝔑")

-- Even/Odd Natural Numbers
#eval Con_toString 𝔈𝔒
#eval Alg 𝔈𝔒 EvenOdd_names
#eval DAlg 𝔈𝔒 EvenOdd_names ["Pe","Po","n","m"]
#eval DAlg 𝔈𝔒 EvenOdd_names ["Pe", "Po", "bc","n","ih","m","ih'"] (some "𝔑")

-- Monoids
#eval Con_toString 𝔐𝔬𝔫
-- #eval Alg 𝔐𝔬𝔫 Monoid_names
#eval Alg 𝔐𝔬𝔫 Monoid_names (some "𝔐𝔬𝔫")
-- #eval DAlg 𝔐𝔬𝔫 Monoid_names

-- Groups
#eval Con_toString 𝔊𝔯𝔭
-- #eval Alg 𝔊𝔯𝔭 Group_names
#eval Alg 𝔊𝔯𝔭 Group_names (some "𝔊𝔯𝔭")
-- #eval DAlg 𝔊𝔯𝔭 Group_names

/-
## Quiver-like structures
-/
-- Quivers
#eval Con_toString 𝔔𝔲𝔦𝔳
#eval Alg 𝔔𝔲𝔦𝔳 Quiv_names
-- #eval DAlg 𝔔𝔲𝔦𝔳 Quiv_names

-- Reflexive quivers
#eval Con_toString 𝔯𝔔𝔲𝔦𝔳
#eval Alg 𝔯𝔔𝔲𝔦𝔳 rQuiv_names
-- #eval DAlg 𝔯𝔔𝔲𝔦𝔳 rQuiv_names

-- Preorders
#eval Con_toString 𝔓𝔯𝔢𝔒𝔯𝔡
#eval Alg 𝔓𝔯𝔢𝔒𝔯𝔡 PreOrd_names (some "𝔓𝔯𝔢𝔒𝔯𝔡")
-- #eval DAlg 𝔓𝔯𝔢𝔒𝔯𝔡 PreOrd_names

-- Setoids
#eval Con_toString 𝔖𝔢𝔱𝔬𝔦𝔡
#eval Alg 𝔖𝔢𝔱𝔬𝔦𝔡 Setoid_names (some "𝔖𝔢𝔱𝔬𝔦𝔡")
-- #eval DAlg 𝔖𝔢𝔱𝔬𝔦𝔡 Setoid_names

-- Categories
#eval Con_toString ℭ𝔞𝔱
#eval Alg ℭ𝔞𝔱 Cat_names (some "ℭ𝔞𝔱")
-- #eval DAlg ℭ𝔞𝔱 Cat_names

-- Groupoids
#eval Con_toString 𝔊𝔯𝔭𝔡
#eval Alg 𝔊𝔯𝔭𝔡 Grpd_names (some "𝔊𝔯𝔭𝔡")
-- #eval DAlg 𝔊𝔯𝔭𝔡 Grpd_names


/-
## Models of Type Theory
-/
-- Categories with Families
#eval Con_toString ℭ𝔴𝔉
#eval Alg ℭ𝔴𝔉 CwF_names (some "ℭ𝔴𝔉")
#eval Alg ℭ𝔴𝔉 CwF_inlinenames
-- #eval DAlg ℭ𝔴𝔉 CwF_names

-- Polarized Categories with Families
#eval Con_toString 𝔓ℭ𝔴𝔉
#eval Alg 𝔓ℭ𝔴𝔉 PCwF_names (some "𝔓ℭ𝔴𝔉")
-- #eval DAlg 𝔓ℭ𝔴𝔉 PCwF_names
