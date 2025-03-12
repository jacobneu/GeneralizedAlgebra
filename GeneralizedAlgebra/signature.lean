import GeneralizedAlgebra.helper

open Nat

mutual
  inductive Tm : Type where
  | VAR : Nat → Tm
  | APP : Tm → Tm → Tm
  | TRANSP : Tm → Tm → Tm → Ty → Tm → Tm → Tm

  inductive Ty : Type where
  | UU : Ty
  | EL : Tm → Ty
  | PI : Tm → Ty → Ty
  | EQ : Tm → Tm → Tm → Ty
end
open Tm Ty

-- Written backwards!
def Con : Type := List Ty
instance : GetElem Con Nat Ty fun (Γ : Con) (i : Nat) => i < Γ.length := List.instGetElemNatLtLength

mutual
  def WkArrTy : Ty → Nat → Ty
  | UU, _ => UU
  | EL X, a => EL (WkArrTm X a)
  | PI X Y, a => PI (WkArrTm X a) (WkArrTy Y (succ a))
  | EQ A t t', a => EQ (WkArrTm A a) (WkArrTm t a) (WkArrTm t' a)
  def WkArrTm : Tm → Nat → Tm
  | VAR n, a => if n ≥ a then VAR (succ n) else VAR n
  | APP f t, a => APP (WkArrTm f a) (WkArrTm t a)
  | TRANSP X s s' Y eq t, a => TRANSP (WkArrTm X a) (WkArrTm s a) (WkArrTm s' a) (WkArrTy Y a) (WkArrTm eq a) (WkArrTm t a)
end

def WkTy : (Γ : Con) → (n : Nat) → n < Γ.length → Ty
| Γ,0,h => WkArrTy (Γ[0]'h) 0
| _::Γ,succ n,h => WkArrTy (WkTy Γ n (lt_of_succ_lt_succ h)) 0

def WkTm (t : Tm) : Tm := WkArrTm t 0

inductive order where
| LESS : order
| EQUAL : order
| GREATER : Nat → order
open order
def GRsucc : order → order
| LESS => LESS
| EQUAL => EQUAL
| GREATER m => GREATER (succ m)

def comparePred : Nat → Nat → order
| 0, 0 => EQUAL
| 0, succ _ => LESS
| succ m, 0 => GREATER m
| succ m, succ n => GRsucc $ comparePred m n

mutual
  def SubstArrTy : Ty → Tm → Nat → Ty
  | UU, _,_ => UU
  | EL X, z, a => EL (SubstArrTm X z a)
  | PI X Y, z, a => PI (SubstArrTm X z a) (SubstArrTy Y z (succ a))
  | EQ A t t', z, a => EQ (SubstArrTm A z a) (SubstArrTm t z a) (SubstArrTm t' z a)
  def SubstArrTm : Tm → Tm → Nat → Tm
  | VAR m, z, a => match comparePred m a with
    | LESS => VAR m
    | EQUAL => z
    | GREATER m' => VAR m'
  | APP f t, z, a => APP (SubstArrTm f z a) (SubstArrTm t z a)
  | TRANSP X s s' Y eq t, z, a => TRANSP (SubstArrTm X z a) (SubstArrTm s z a) (SubstArrTm s' z a) (SubstArrTy Y z (succ a)) (SubstArrTm eq z a) (SubstArrTm t z a)
end

def SubstTy := λ T t => SubstArrTy T t 0
def SubstTm := λ t t' => SubstArrTm t t' 0


structure indData where
    (Con_D : Con → Type)
    (Ty_D : (Γ : Con) → Con_D Γ → Ty → Type)
    (Tm_D : (Γ : Con) → (Γ_D : Con_D Γ) → (A : Ty) → Ty_D Γ Γ_D A → Tm → Type)
    (nil_D : Con_D [])
    (cons_D : (Γ : Con) → (Γ_D : Con_D Γ) → (A : Ty) → (A_D : Ty_D Γ Γ_D A) → Con_D (A::Γ))
    (UU_D : (Γ : Con) → (Γ_D : Con_D Γ) → Ty_D Γ Γ_D UU)
    (EL_D : (Γ : Con) → (Γ_D : Con_D Γ) →
            (X : Tm) → Tm_D Γ Γ_D UU (UU_D Γ Γ_D) X →
            Ty_D Γ Γ_D (EL X))
    (PI_D : (Γ : Con) → (Γ_D : Con_D Γ) →
            (X : Tm) → (X_D : Tm_D Γ Γ_D UU (UU_D Γ Γ_D) X) →
            (Y : Ty) → Ty_D (EL X :: Γ) (cons_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D)) Y →
            Ty_D Γ Γ_D (PI X Y))
    (EQ_D : (Γ : Con) → (Γ_D : Con_D Γ) →
            (X : Tm) → (X_D : Tm_D Γ Γ_D UU (UU_D Γ Γ_D) X) →
            (s : Tm) → (s_D : Tm_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D) s) →
            (s' : Tm) → (s'_D : Tm_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D) s') →
            Ty_D Γ Γ_D (EQ X s s'))
    (VAR_D :(Γ : Con) → (Γ_D : Con_D Γ) →
            (n : Nat) → (h : n < List.length Γ) →
            (A_D : Ty_D Γ Γ_D (WkTy Γ n h)) →
            Tm_D Γ Γ_D (WkTy Γ n h) A_D (VAR n))
    (APP_D :(Γ : Con) → (Γ_D : Con_D Γ) →
            (X : Tm) → (X_D : Tm_D Γ Γ_D UU (UU_D Γ Γ_D) X) →
            (Y : Ty) → (Y_D : Ty_D (EL X :: Γ) (cons_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D)) Y) →
            (f : Tm) → (f_D : Tm_D Γ Γ_D (PI X Y) (PI_D Γ Γ_D X X_D Y Y_D) f) →
            (t : Tm) → (t_D : Tm_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D) t) →
            (Yt_D : Ty_D Γ Γ_D (SubstTy Y t)) →
            Tm_D Γ Γ_D (SubstTy Y t) Yt_D (APP f t))
    (TRANSP_D :(Γ : Con) → (Γ_D : Con_D Γ) →
            (X : Tm) → (X_D : Tm_D Γ Γ_D UU (UU_D Γ Γ_D) X) →
            (s : Tm) → (s_D : Tm_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D) s) →
            (s' : Tm) → (s'_D : Tm_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D) s') →
            (Y : Ty) → (Y_D : Ty_D (EL X :: Γ) (cons_D Γ Γ_D (EL X) (EL_D Γ Γ_D X X_D)) Y) →
            (Ys_D : Ty_D Γ Γ_D (SubstTy Y s)) → (Ys'_D : Ty_D Γ Γ_D (SubstTy Y s')) →
            (p : Tm) → (p_D : Tm_D Γ Γ_D (EQ X s s') (EQ_D Γ Γ_D X X_D s s_D s' s'_D) p) →
            (k : Tm) → Tm_D Γ Γ_D (SubstTy Y s) Ys_D k →
            Tm_D Γ Γ_D (SubstTy Y s') Ys'_D (TRANSP X s s' Y eq k))

mutual
    def elim (P : indData) : (Γ : Con) → P.Con_D Γ
    | [] => P.nil_D
    | A::Γ => P.cons_D _ (elim _ _) _ (elimTy _ _ _ _)

    def elimTy (P : indData) (Γ : Con) (Γ_D : P.Con_D Γ) : (A : Ty) → P.Ty_D Γ Γ_D A
    | UU => P.UU_D Γ Γ_D
    | EL X => P.EL_D _ _ _ (elimTm _ _ _ _ _ _)
    | PI X Y => P.PI_D _ _ _ (elimTm _ _ _ _ _ _) _ (elimTy _ _ _ _)
    | EQ X s s' => P.EQ_D _ _ _ (elimTm _ _ _ _ _ _) _ (elimTm _ _ _ _ _ _) _ (elimTm _ _ _ _ _ _)

    def elimTm (P : indData) (Γ : Con) (Γ_D : P.Con_D Γ) (A : Ty) (A_D : P.Ty_D Γ Γ_D A) : (t : Tm) → P.Tm_D Γ Γ_D A A_D t
    | APP f t => P.APP_D Γ Γ_D _ _ _ _ _ _ _ (elimTm _ _ _ _ _ _) _
    | TRANSP X s s' Y eq k => _ --P.TRANSP_D Γ Γ_D _ _ _ _ _ _ _ _ (elimTy _ _ _ _) (elimTy _ _ _ _) _ _ _ _
    | VAR n => _
end

-- def x := @APP P''' (SUCC $ SUCC ZERO) UU (SUCC ZERO) (ZERO)
-- def Q := P'' ▷ PI (SUCC ZERO) (@EL P''' (@APP P''' _ _ _ _))
-- #reduce P'''

-- #eval len
--     ⋄ ▷ UU ▷ PI ZERO UU
    -- ▷ PI (SUCC ZERO) (EL (@APP P''' (SUCC $ SUCC ZERO) UU (SUCC ZERO) (ZERO)))
    --▷ (PI (SUCC ZERO) (EL (APP (SUCC ZERO) _ )))
    -- ▷ (PI ZERO (PI (SUCC ZERO) (EL $ SUCC $ SUCC $ ZERO)))
    -- ▷ (PI (SUCC ZERO) (EQ (SUCC $ SUCC ZERO) (APP (SUCC $ ZERO) (APP _ _)) ZERO))
    -- ▷ (EL $ SUCC $ ZERO)
    -- ▷ (PI (SUCC $ SUCC $ ZERO) (EQ (SUCC $ SUCC $ SUCC $ ZERO) ZERO (APP (APP (_) ZERO) (SUCC ZERO))))
-- notation t " [ " σ " ]t " => SUBST_Tm σ t
