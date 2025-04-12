import «GeneralizedAlgebra».AlgPrinting
import «GeneralizedAlgebra».ConPrinting

import «GeneralizedAlgebra».signatures.set
import «GeneralizedAlgebra».signatures.pointed
import «GeneralizedAlgebra».signatures.bipointed
import «GeneralizedAlgebra».signatures.nat
import «GeneralizedAlgebra».signatures.evenodd
import «GeneralizedAlgebra».signatures.quiver
import «GeneralizedAlgebra».signatures.refl_quiver
import «GeneralizedAlgebra».signatures.monoid
import «GeneralizedAlgebra».signatures.group
import «GeneralizedAlgebra».signatures.preorder
import «GeneralizedAlgebra».signatures.setoid
import «GeneralizedAlgebra».signatures.category
import «GeneralizedAlgebra».signatures.groupoid
import «GeneralizedAlgebra».signatures.CwF
import «GeneralizedAlgebra».signatures.CwF_unit
import «GeneralizedAlgebra».signatures.CwF_bool
import «GeneralizedAlgebra».signatures.CwF_Pi
import «GeneralizedAlgebra».signatures.PCwF

structure printData where
  (gat : GAT)
  (gatName : String)
  (gatNamePlain : String)
  (inlineDAlgNames : Option (List String))
  (recordDAlgNames : Option (List String))
  (recordAlgNamesAlt : Option (List String))

def printDAlgInline (X : printData) := match X.inlineDAlgNames with
  | none => none
  | some nameList => DAlg X.gat none nameList
def printDAlgRecord (X : printData) := match X.recordDAlgNames, X.recordAlgNamesAlt with
  | none,_ => none
  | some nameList, none => DAlg X.gat (some X.gatName) nameList
  | some nameList, some nameDList => DAlg X.gat (some X.gatName) nameList nameDList

def allGATs : List printData := [
  ⟨𝔖𝔢𝔱,"𝔖𝔢𝔱","set",["P"],["P"],none⟩,
  ⟨𝔓,"𝔓","pointed",["P"],["P","p₀"],some ["X","x₀"]⟩,
  ⟨𝔅,"𝔅","bipointed",["P"],["P","p₀","p₁"],none⟩,
  ⟨𝔑,"𝔑","nat",["P","n"],["P","base_case","n","ind_step"],some ["N","z","s"]⟩,
  ⟨𝔈𝔒,"𝔈𝔒","evenodd",["Pe","Po","n","m"],["Pe", "Po", "bc","n","ih","m","ih'"],none⟩,
  ⟨𝔐𝔬𝔫,"𝔐𝔬𝔫","monoid",none,none,none⟩,
  ⟨𝔊𝔯𝔭,"𝔊𝔯𝔭","group",none,none,none⟩,
  ⟨𝔔𝔲𝔦𝔳,"𝔔𝔲𝔦𝔳","quiver",none,none,none⟩,
  ⟨𝔯𝔔𝔲𝔦𝔳,"𝔯𝔔𝔲𝔦𝔳","refl-quiver",none,none,none⟩,
  ⟨𝔓𝔯𝔢𝔒𝔯𝔡,"𝔓𝔯𝔢𝔒𝔯𝔡","preorder",none,none,none⟩,
  ⟨𝔖𝔢𝔱𝔬𝔦𝔡,"𝔖𝔢𝔱𝔬𝔦𝔡","setoid",none,none,none⟩,
  ⟨ℭ𝔞𝔱,"ℭ𝔞𝔱","category",none,none,none⟩,
  ⟨𝔊𝔯𝔭𝔡,"𝔊𝔯𝔭𝔡","groupoid",none,none,none⟩,
  ⟨ℭ𝔴𝔉,"ℭ𝔴𝔉","CwF",none,none,none⟩,
  ⟨ℭ𝔴𝔉₁,"ℭ𝔴𝔉₁","CwF+unit",none,none,none⟩,
  ⟨ℭ𝔴𝔉₂,"ℭ𝔴𝔉₂","CwF+bool",none,none,none⟩,
  ⟨ℭ𝔴𝔉pi,"ℭ𝔴𝔉pi","CwF+Pi",none,none,none⟩,
  ⟨𝔓ℭ𝔴𝔉,"𝔓ℭ𝔴𝔉","PCwF",none,none,none⟩
]

/-
## Basic structures
-/
-- Sets
def SET := allGATs[0]
#eval SET.gat
#eval Alg SET.gat
#eval Alg SET.gat (some SET.gatName)
#eval printDAlgInline SET
#eval printDAlgRecord SET

-- Pointed sets
def POINTED := allGATs[1]
#eval POINTED.gat
#eval Alg POINTED.gat
#eval Alg POINTED.gat (some POINTED.gatName)
#eval printDAlgInline POINTED
#eval printDAlgRecord POINTED

-- Bipointed sets
def BIPOINTED := allGATs[2]
#eval BIPOINTED.gat
#eval Alg BIPOINTED.gat
#eval Alg BIPOINTED.gat (some BIPOINTED.gatName)
#eval printDAlgInline BIPOINTED
#eval printDAlgRecord BIPOINTED

-- Natural numbers
def NAT := allGATs[3]
#eval NAT.gat
#eval Alg NAT.gat
#eval Alg NAT.gat (some NAT.gatName)
#eval printDAlgInline NAT
#eval printDAlgRecord NAT

-- Even/Odd Natural Numbers
def EO := allGATs[4]
#eval EO.gat
#eval Alg EO.gat
#eval Alg EO.gat (some EO.gatName)
#eval printDAlgInline EO
#eval printDAlgRecord EO

-- Monoids
def MON := allGATs[5]
#eval MON.gat
#eval Alg MON.gat (some MON.gatName)

-- Groups
def GRP := allGATs[6]
#eval GRP.gat
#eval Alg GRP.gat (some GRP.gatName)


/-
## Quiver-like structures
-/
-- Quivers
def QUIV := allGATs[7]
#eval QUIV.gat
#eval Alg QUIV.gat (some QUIV.gatName)

-- -- Reflexive quivers
def RQUIV := allGATs[8]
#eval RQUIV.gat
#eval Alg RQUIV.gat (some RQUIV.gatName)

-- -- Preorders
def PREORD := allGATs[9]
#eval PREORD.gat
#eval Alg PREORD.gat (some PREORD.gatName)

-- -- Setoids
def SETOID := allGATs[10]
#eval SETOID.gat
#eval Alg SETOID.gat (some SETOID.gatName)

-- -- Categories
def CAT := allGATs[11]
#eval CAT.gat
#eval Alg CAT.gat (some CAT.gatName)

-- -- Groupoids
def GRPD := allGATs[12]
#eval GRPD.gat
#eval Alg GRPD.gat (some GRPD.gatName)


/-
## Models of Type Theory
-/
-- Categories with Families
def CWF := allGATs[13]
#eval CWF.gat
#eval Alg CWF.gat (some CWF.gatName)
#eval Alg CWF.gat none CwF_inlinenames
-- Categories with Families + unit
def CWF₁ := allGATs[14]
#eval CWF₁.gat
#eval Alg CWF₁.gat (some CWF₁.gatName)

-- Categories with Families + bool
def CWF₂ := allGATs[15]
#eval CWF₂.gat
#eval Alg CWF₂.gat (some CWF₂.gatName)

-- Categories with Families + Pi
def CWFpi := allGATs[16]
#eval CWFpi.gat
#eval Alg CWFpi.gat (some CWFpi.gatName)

-- -- Polarized Categories with Families
def PCWF := allGATs[17]
#eval PCWF.gat
#eval Alg PCWF.gat (some PCWF.gatName)
