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
#eval 𝔖𝔢𝔱
#eval Alg 𝔖𝔢𝔱
#eval DAlg 𝔖𝔢𝔱 none ["P"]
#eval DAlg 𝔖𝔢𝔱 (some "𝔖𝔢𝔱") ["P"]

-- Pointed sets
#eval 𝔓
#eval Alg 𝔓
#eval DAlg 𝔓 none ["P"]
#eval DAlg 𝔓 (some "𝔓") ["P","p₀"] ["X","x₀"]

-- Bipointed sets
#eval 𝔅
#eval Alg 𝔅
#eval DAlg 𝔅 none ["P"]
#eval DAlg 𝔅 (some "𝔅") ["P","p₀","p₁"]

-- Natural numbers
#eval 𝔑
#eval Alg 𝔑
#eval DAlg 𝔑 none ["P","n"] ["N","z","s"]
#eval DAlg 𝔑 (some "𝔑") ["P","base_case","n","ind_step"]

-- Even/Odd Natural Numbers
#eval 𝔈𝔒
#eval Alg 𝔈𝔒
#eval DAlg 𝔈𝔒 none ["Pe","Po","n","m"]
#eval DAlg 𝔈𝔒 (some "𝔑") ["Pe", "Po", "bc","n","ih","m","ih'"]

-- Monoids
#eval 𝔐𝔬𝔫
-- #eval Alg 𝔐𝔬𝔫 none
#eval Alg 𝔐𝔬𝔫 (some "𝔐𝔬𝔫")

-- Groups
#eval 𝔊𝔯𝔭
-- #eval Alg 𝔊𝔯𝔭 none
#eval Alg 𝔊𝔯𝔭 (some "𝔊𝔯𝔭")

/-
## Quiver-like structures
-/
-- Quivers
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


/-
## Models of Type Theory
-/
-- Categories with Families
#eval ℭ𝔴𝔉
#eval Alg ℭ𝔴𝔉 (some "ℭ𝔴𝔉")
#eval Alg ℭ𝔴𝔉 none CwF_inlinenames

-- -- Polarized Categories with Families
#eval 𝔓ℭ𝔴𝔉
#eval Alg 𝔓ℭ𝔴𝔉 (some "𝔓ℭ𝔴𝔉")
