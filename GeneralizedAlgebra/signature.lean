import GeneralizedAlgebra.helper
import Lean

open Lean Meta
open Nat

inductive preTm : Type where
| preVAR : Nat → preTm
| preAPP : preTm → preTm → preTm
| preTRANSP : preTm → preTm → preTm

inductive preTy : Type where
| preUU : preTy
| preEL : preTm → preTy
| prePI : preTm → preTy → preTy
| preEQ : preTm → preTm → preTy

open preTm preTy

-- Written backwards!
def preCon : Type := List preTy
instance : GetElem preCon Nat preTy fun (Γ : preCon) (i : Nat) => i < Γ.length := List.instGetElemNatLtLength
def preEXTEND (Γ : preCon) (A : preTy) := A :: Γ
def preEMPTY : preCon := []

def preWkTmArr : Nat → preTm → preTm
| a, preVAR n => if n < a then preVAR n else preVAR (succ n)
| a, preAPP f t => preAPP (preWkTmArr a f) (preWkTmArr a t)
| a, preTRANSP eq t => preTRANSP (preWkTmArr a eq) (preWkTmArr a t)

def preWkTyArr : Nat → preTy → preTy
| _, preUU => preUU
| a, preEL t => preEL (preWkTmArr a t)
| a, preEQ s t => preEQ (preWkTmArr a s) (preWkTmArr a t)
| a, prePI X Y => prePI (preWkTmArr a X) (preWkTyArr (succ a) Y)

def preWkTm := preWkTmArr 0
def preWkTy := preWkTyArr 0


def substTm : Nat → preTm → preTm → preTm
| a, s, preVAR n =>
  match compare n a with
    | Ordering.lt => preVAR n
    | Ordering.eq => s
    | Ordering.gt => preVAR (n - 1)
| a, s, preAPP f t => preAPP (substTm a s f) (substTm a s t)
| a, s, preTRANSP eq t => preTRANSP (substTm a s eq) (substTm a s t)

def substTy : Nat → preTm → preTy → preTy
| _, _, preUU => preUU
| a, s, preEL t => preEL (substTm a s t)
| a, s, preEQ s' t => preEQ (substTm a s s') (substTm a s t)
| a, s, prePI X Y => prePI (substTm a s X) (substTy (succ a) s Y)

inductive preArg : Type where
-- | preImpl : String → preTy → preArg
| preExpl : String → preTy → preArg
| preAnon : preTy → preArg
open preArg

structure GATdata where
  (con : preCon)
  (topnames : List String)
  (telescopes : List (List preArg × preTy))
