import GeneralizedAlgebra.signature
open preCon preSub preTy preTm

-- pointed
def 𝔓 : GAT_sig := X : U, x : X
#reduce 𝔓

def QQ : GAT_sig :=
    V : U,
    E : V ⇒ V ⇒ U
#reduce QQ

def 𝔑 : GAT_sig :=
  include 𝔓 as (Nat,zero);
  include 𝔓 as (Nat',zero');
  include 𝔓 as (Nat'',zero'');
  include 𝔓 as (Nat''',zero''');
  include 𝔓 as (Nat'''',zero'''');
  include 𝔓 as (Nat''''',zero''''');
  suc : Nat ⇒ Nat
  , foo : Nat ⇒ Nat
  , foo' : Nat ⇒ Nat
  , foo'' : Nat ⇒ Nat
#reduce 𝔑
