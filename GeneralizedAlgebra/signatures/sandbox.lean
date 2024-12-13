import GeneralizedAlgebra.signatures.monoid
import GeneralizedAlgebra.signatures.pointed
import GeneralizedAlgebra.signatures.quiver
import GeneralizedAlgebra.signatures.refl_quiver_copy
import GeneralizedAlgebra.signatures.category_plain


#eval Con_toString 𝔓
#eval Con_toString 𝔐𝔬𝔫
#eval Con_toString 𝔔𝔲𝔦𝔳
#eval Con_toString 𝔯𝔔𝔲𝔦𝔳
#eval Con_toString ℭ𝔞𝔱
#eval Alg 𝔓
#eval Alg 𝔐𝔬𝔫
-- open preCon preSub preTy preTm

-- -- pointed
-- def 𝔓 : GAT_sig := X : U, x : X
-- #reduce 𝔓

-- def QQ : GAT_sig :=
--     V : U,
--     E : V ⇒ V ⇒ U
-- #reduce QQ

-- def 𝔑 : GAT_sig :=
--   include 𝔓 as (Nat,zero);
--   include 𝔓 as (Nat',zero');
--   include 𝔓 as (Nat'',zero'');
--   include 𝔓 as (Nat''',zero''');
--   include 𝔓 as (Nat'''',zero'''');
--   include 𝔓 as (Nat''''',zero''''');
--   suc : Nat ⇒ Nat
--   , foo : Nat ⇒ Nat
--   , foo' : Nat ⇒ Nat
--   , foo'' : Nat ⇒ Nat
-- #reduce 𝔑
