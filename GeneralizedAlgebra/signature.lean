import GeneralizedAlgebra.helper

open Nat

mutual
  inductive Tm : Type where
  | VAR : Nat → Tm
  | APP : Tm → Ty → Tm → Tm → Tm
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
  | APP X Y f t, a => APP (WkArrTm X a) (WkArrTy Y (succ a)) (WkArrTm f a) (WkArrTm t a)
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
  | VAR m, z, a =>
  match comparePred m a with
    | LESS => VAR m
    | EQUAL => z
    | GREATER m' => VAR m'
  | APP X Y f t, z, a => APP (SubstArrTm X z a) (SubstArrTy Y z (succ a)) (SubstArrTm f z a) (SubstArrTm t z a)
  | TRANSP X s s' Y eq t, z, a => TRANSP (SubstArrTm X z a) (SubstArrTm s z a) (SubstArrTm s' z a) (SubstArrTy Y z (succ a)) (SubstArrTm eq z a) (SubstArrTm t z a)
end

def varElim {motive : Tm → Type} (m : Nat) (z : Tm) (mL : motive (VAR m)) (mE : motive z) (mG : (m' : Nat) → motive (VAR m')) (a : Nat) : motive (SubstArrTm (VAR m) z a) :=
by
    cases (comparePred m a)
    dsimp[SubstArrTm]
    sorry
    sorry
    sorry



def substAt : (Γ : Con) → (z : Tm) → (a : Nat) → (a < Γ.length) → Con
| _::Γ,_,0,_ => Γ
| A::Γ,z,succ a,h => SubstArrTy A z (a) :: substAt Γ z a (lt_of_succ_lt_succ h)

def trunc : (Γ : Con) → (a : Nat) → (a < Γ.length) → Con
| _::Γ,succ a',h => trunc Γ a' (lt_of_succ_lt_succ h)
| _::Γ,0,_ => Γ

def SubstTy := λ T t => SubstArrTy T t 0
def SubstTm := λ t t' => SubstArrTm t t' 0

mutual
  inductive goodCon : Con → Type where
  | goodNil : goodCon []
  | goodCons : ∀ {Γ : Con}{A : Ty}, goodTy Γ A → goodCon Γ → goodCon (A::Γ)

  inductive goodTy : Con → Ty → Type where
  | goodUU : ∀ {Γ : Con}, goodTy Γ UU
  | goodEL : ∀ {Γ : Con}{X : Tm}, goodTm Γ UU X → goodTy Γ (EL X)
  | goodPI : ∀ {Γ : Con}{X : Tm}{Y : Ty}, goodTm Γ UU X → goodTy (EL X::Γ) Y → goodTy Γ (PI X Y)
  | goodEQ : ∀ {Γ : Con}{X : Tm}{t t' : Tm}, goodTm Γ UU X → goodTm Γ (EL X) t → goodTm Γ (EL X) t' → goodTy Γ (EQ X t t')

  inductive goodTm : Con → Ty → Tm → Type where
  | goodVAR : ∀ {Γ : Con}(n : Nat), (h : n < Γ.length) → goodTm Γ (WkTy Γ n h) (VAR n)
  | goodAPP : ∀ {Γ : Con}{X : Tm}{Y : Ty}{f t : Tm}, goodTm Γ UU X → goodTy (EL X::Γ) Y → goodTm Γ (PI X Y) f → goodTm Γ (EL X) t → goodTm Γ (SubstTy Y t) (APP X Y f t)
  | goodTRANSP : ∀ {Γ : Con}{X : Tm}{s s' : Tm}{Y : Ty}{eq t : Tm},
      goodTm Γ UU X → goodTm Γ (EL X) s → goodTm Γ (EL X) s' → goodTy (EL X::Γ) Y → goodTm Γ (EQ X s s') eq → goodTm Γ (SubstTy Y s) t → goodTm Γ (SubstTy Y s') (TRANSP X s s' Y eq t)
end

open goodTm goodTy goodCon
mutual
  def goodSubstArrTy  {Γ : Con} : (A : Ty) → (z : Tm) → (a : Nat) → (h : a < Γ.length) → goodTy Γ A → goodTm (trunc Γ a h) (Γ[a]'h) z → goodTy (substAt Γ z a h) (SubstArrTy A z a)
  | UU, _,_,_,_,_ => goodUU
  | EL X,z,a,h,goodEL gX,gz => goodEL (goodSubstArrTm X z a h goodUU gX gz)
  | EQ X t t',z,a,h,goodEQ gX gt gt',gz => goodEQ (goodSubstArrTm X z a h goodUU gX gz) (goodSubstArrTm t z a h (goodEL gX) gt gz) (goodSubstArrTm t' z a h (goodEL gX) gt' gz)
  | PI X Y, z,a,h,goodPI gX gY,gz => goodPI (goodSubstArrTm X z a h goodUU gX gz) (@goodSubstArrTy (EL X :: Γ) Y z (succ a) (succ_lt_succ h) gY gz)

  def goodSubstArrTm {Γ : Con}{A : Ty} : (t : Tm) → (z : Tm) → (a : Nat) → (h : a < Γ.length) → goodTy Γ A → goodTm Γ A t → goodTm (trunc Γ a h) (Γ[a]'h) z → goodTm (substAt Γ z a h) (SubstArrTy A z a) (SubstArrTm t z a)
  | APP X Y f t, z, a, h, _ , goodAPP gX gY gf gt,gz =>
        goodSubstArrTm _ _ _ _ (@goodSubstArrTy (EL X::Γ) Y t 0 (zero_lt_succ Γ.length) gY gt) (goodAPP gX gY gf gt) gz
  | TRANSP X s s' Y eq t, z, a, h, _, goodTRANSP gX gs gs' gY geq gt,gz =>
        goodSubstArrTm _ _ _ _ (@goodSubstArrTy (EL X::Γ) Y s' 0 (zero_lt_succ Γ.length) gY gs') (goodTRANSP gX gs gs' gY geq gt) gz
  | VAR m, z, a, h, gw, gv,gz => varElim _ _ _ _ _ _
end

def goodSubst {Γ : Con}{X : Tm}{s : Tm}{Y : Ty} (gs : goodTm Γ (EL X) s) (gY : goodTy (EL X::Γ) Y) : goodTy Γ (SubstTy Y s) :=
        @goodSubstArrTy (EL X :: Γ) Y s 0 (zero_lt_succ Γ.length) gY gs


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
            Tm_D Γ Γ_D (SubstTy Y t) Yt_D (APP X Y f t))
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
    def elim (P : indData) : (Γ : Con) → goodCon Γ → P.Con_D Γ
    | [],_ => P.nil_D
    | A::Γ,goodCons gA gΓ => P.cons_D _ (elim _ _ gΓ) _ (elimTy _ _ _ _ gΓ gA)

    -- def dispGetElem (P : indData) (Γ : Con) (n : Nat) (h : n < List.length Γ) :
    --     Σ (Γ_D : P.Con_D Γ), P.Ty_D Γ Γ_D (WkTy Γ n h) :=  ⟨elim _ _,elimTy _ _ _ _ _⟩

    -- def dispWkTy : (P : indData) →
    --     (Γ : Con) → (Γ_D : P.Con_D Γ) →
    --     (A : Ty) → (A_D : P.Ty_D Γ Γ_D A) →
    --     (n : Nat) → (h : n < List.length Γ) →
    --     P.Ty_D Γ Γ_D (WkTy Γ n h) →
    --     P.Ty_D (A::Γ) (P.cons_D _ Γ_D _ A_D) (WkTy (A::Γ) (succ n) (succ_lt_succ h)) := _


    def elimTy (P : indData) (Γ : Con) (Γ_D : P.Con_D Γ) : (A : Ty) → goodCon Γ → goodTy Γ A → P.Ty_D Γ Γ_D A
    | UU,_,goodUU => P.UU_D Γ Γ_D
    | EL X,gΓ,goodEL gX => P.EL_D _ _ _ (elimTm _ _ _ _ _ _ gΓ goodUU gX)
    | PI X Y,gΓ,goodPI gX gY => P.PI_D _ _ _ (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTy _ _ _ _ (goodCons (goodEL gX) gΓ) gY)
    | EQ X s s',gΓ,goodEQ gX gs gs' => P.EQ_D _ _ _ (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs')

    def elimTm (P : indData) (Γ : Con) (Γ_D : P.Con_D Γ) : (A : Ty) → (A_D : P.Ty_D Γ Γ_D A) → (t : Tm) → goodCon Γ → goodTy Γ A → goodTm Γ A t → P.Tm_D Γ Γ_D A A_D t
    | _,_,APP X Y f t,gΓ,_, @goodAPP _ _ _ _ _ gX gY gf gt => P.APP_D Γ Γ_D X (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTy _ _ _ _ (goodCons (goodEL gX) gΓ) gY) _ (elimTm _ _ _ _ _ _ gΓ (goodPI gX gY) gf) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gt) _
    | _,_,TRANSP X s s' Y eq k,gΓ,_,goodTRANSP gX gs gs' gY geq gk => P.TRANSP_D Γ Γ_D _ (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs') _ (elimTy _ _ _ _ (goodCons (goodEL gX) gΓ) gY) (elimTy _ _ _ _ gΓ (goodSubst gs gY)) _ _ (elimTm _ _ _ _ _ _ gΓ (goodEQ gX gs gs') geq) _ (elimTm _ _ _ _ (elimTy _ _ _ _ _ _) _ gΓ (goodSubst gs gY) gk)
    | _,_,VAR n, gΓ,_, (goodVAR _ h) => P.VAR_D Γ Γ_D n _ _
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
