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


def preWkTm : preTm → preTm
| preVAR n => preVAR (succ n)
| preAPP f t => preAPP (preWkTm f) (preWkTm t)
| preTRANSP eq t => preTRANSP (preWkTm eq) (preWkTm t)

inductive preArg : Type where
| preImpl : String → preTy → preArg
| preExpl : String → preTy → preArg
| preAnon : preTy → preArg
open preArg

structure GATdata where
  (con : preCon)
  (topnames : List String)
  (telescopes : List (List preArg × preTy))
