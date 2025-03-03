import GeneralizedAlgebra.AlgPrinting
import GeneralizedAlgebra.ConPrinting

import GeneralizedAlgebra.signatures.pointed
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


-- Pointed sets
#eval 𝔓
#eval Alg 𝔓
#eval DAlg 𝔓 none ["P"]
#eval DAlg 𝔓 (some "𝔓") ["P","p₀"] ["X","x₀"]

-- Natural numbers
#eval 𝔑
#eval Alg 𝔑
#eval DAlg 𝔑 none ["P","n"] ["N","z","s"]
#eval DAlg 𝔑 (some "𝔑") ["P","base_case","n","ind_step"]

-- -- Quivers
#eval 𝔔𝔲𝔦𝔳
#eval Alg 𝔔𝔲𝔦𝔳

-- -- Reflexive quivers
#eval 𝔯𝔔𝔲𝔦𝔳
#eval Alg 𝔯𝔔𝔲𝔦𝔳

-- -- Monoids
#eval 𝔐𝔬𝔫
#eval Alg 𝔐𝔬𝔫 (some "𝔐𝔬𝔫")

-- -- Preorders
#eval 𝔓𝔯𝔢𝔒𝔯𝔡
#eval Alg 𝔓𝔯𝔢𝔒𝔯𝔡 (some "𝔓𝔯𝔢𝔒𝔯𝔡")

-- -- Setoids
#eval 𝔖𝔢𝔱𝔬𝔦𝔡
#eval Alg 𝔖𝔢𝔱𝔬𝔦𝔡 (some "𝔖𝔢𝔱𝔬𝔦𝔡")

-- -- Categories
#eval ℭ𝔞𝔱
#eval Alg ℭ𝔞𝔱 (some "ℭ𝔞𝔱")

-- -- Groupoids
#eval 𝔊𝔯𝔭𝔡
#eval Alg 𝔊𝔯𝔭𝔡 (some "𝔊𝔯𝔭𝔡")

-- -- Categories with Families
#eval ℭ𝔴𝔉
#eval Alg ℭ𝔴𝔉 (some "ℭ𝔴𝔉")
#eval Alg ℭ𝔴𝔉 none CwF_inlinenames

-- -- Polarized Categories with Families
#eval 𝔓ℭ𝔴𝔉
#eval Alg 𝔓ℭ𝔴𝔉 (some "𝔓ℭ𝔴𝔉")
