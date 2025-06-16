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
def EXTEND (Γ : Con) (A : Ty) := A :: Γ
def EMPTY : Con := []

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

def WknTy : (Γ : Con) → (n : Nat) → n < Γ.length → Ty
| Γ,0,h => WkArrTy (Γ[0]'h) 0
| _::Γ,succ n,h => WkArrTy (WknTy Γ n (lt_of_succ_lt_succ h)) 0

mutual
  def WkTy : Ty → Ty
  | UU => UU
  | EL X => EL (WkTm X)
  | EQ A t t' => EQ (WkTm A) (WkTm t) (WkTm t')
  | T =>  WkArrTy T 0
  def WkTm : Tm →  Tm
  | VAR n => VAR (succ n)
  | TRANSP X s s' Y eq t => TRANSP (WkTm X) (WkTm s) (WkTm s') (WkTy Y) (WkTm eq) (WkTm t)
  | t => WkArrTm t 0
end

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
    if m < a then VAR m else
    if m = a then z
             else VAR (pred m)
  -- match comparePred m a with
  --   | LESS => VAR m
  --   | EQUAL => z
  --   | GREATER m' => VAR m'
  | APP X Y f t, z, a => APP (SubstArrTm X z a) (SubstArrTy Y z (succ a)) (SubstArrTm f z a) (SubstArrTm t z a)
  | TRANSP X s s' Y eq t, z, a => TRANSP (SubstArrTm X z a) (SubstArrTm s z a) (SubstArrTm s' z a) (SubstArrTy Y z (succ a)) (SubstArrTm eq z a) (SubstArrTm t z a)
end

-- def varElim {motive : Tm → Type} (m : Nat) (z : Tm) (mL : motive (VAR m)) (mE : motive z) (mG : (m' : Nat) → motive (VAR m')) (a : Nat) : motive (SubstArrTm (VAR m) z a) :=
-- by
--     cases (comparePred m a)
--     dsimp[SubstArrTm]
--     sorry
--     sorry
--     sorry



def substAt : (Γ : Con) → (z : Tm) → (a : Nat) → (a < Γ.length) → Con
| _::Γ,_,0,_ => Γ
| A::Γ,z,succ a,h => SubstArrTy A z (a) :: substAt Γ z a (lt_of_succ_lt_succ h)

def trunc : (Γ : Con) → (a : Nat) → (a < Γ.length) → Con
| _::Γ,succ a',h => trunc Γ a' (lt_of_succ_lt_succ h)
| _::Γ,0,_ => Γ

def SubstTy := λ T t => SubstArrTy T t 0
def SubstTm := λ t t' => SubstArrTm t t' 0

-- mutual
--   inductive goodCon : Con → Type where
--   | goodNil : goodCon []
--   | goodCons : ∀ {Γ : Con}{A : Ty}, goodTy Γ A → goodCon Γ → goodCon (A::Γ)

--   inductive goodTy : Con → Ty → Type where
--   | goodUU : ∀ {Γ : Con}, goodTy Γ UU
--   | goodEL : ∀ {Γ : Con}{X : Tm}, goodTm Γ UU X → goodTy Γ (EL X)
--   | goodPI : ∀ {Γ : Con}{X : Tm}{Y : Ty}, goodTm Γ UU X → goodTy (EL X::Γ) Y → goodTy Γ (PI X Y)
--   | goodEQ : ∀ {Γ : Con}{X : Tm}{t t' : Tm}, goodTm Γ UU X → goodTm Γ (EL X) t → goodTm Γ (EL X) t' → goodTy Γ (EQ X t t')

--   inductive goodTm : Con → Ty → Tm → Type where
--   -- | goodVAR : ∀ {Γ : Con}(n : Nat), (h : n < Γ.length) → goodTm Γ (WknTy Γ n h) (VAR n)
--   | goodVAR0 : ∀ {Γ : Con}{A : Ty}, goodTy Γ A → goodTm (A::Γ) (WkTy A) (VAR 0)
--   | goodSUCC : ∀ {Γ : Con}{A : Ty}{B : Ty}{m : Nat}, goodTy Γ A → goodTm Γ A (VAR m) → goodTm (B::Γ) (WkTy A) (VAR (succ m))
--   | goodAPP : ∀ {Γ : Con}{X : Tm}{Y : Ty}{f t : Tm}, goodTm Γ UU X → goodTy (EL X::Γ) Y → goodTm Γ (PI X Y) f → goodTm Γ (EL X) t → goodTm Γ (SubstTy Y t) (APP X Y f t)
--   | goodTRANSP : ∀ {Γ : Con}{X : Tm}{s s' : Tm}{Y : Ty}{eq t : Tm},
--       goodTm Γ UU X → goodTm Γ (EL X) s → goodTm Γ (EL X) s' → goodTy (EL X::Γ) Y → goodTm Γ (EQ X s s') eq → goodTm Γ (SubstTy Y s) t → goodTm Γ (SubstTy Y s') (TRANSP X s s' Y eq t)
-- end


-- open goodTm goodTy goodCon

theorem UU_stable : UU = WkTy UU := Eq.refl _

-- def good_Set : goodCon [UU] := by
--   apply goodCons
--   exact goodUU
--   exact goodNil

-- def good_pointed : goodCon [EL (VAR 0),UU] := by
--   apply goodCons
--   apply goodEL
--   apply goodVAR0
--   apply goodUU
--   exact good_Set

-- def good_nat : goodCon [PI (VAR 1) (EL (VAR 2)),EL (VAR 0),UU] := by
--   apply goodCons
--   apply goodPI
--   rw [UU_stable]
--   apply goodSUCC
--   apply goodUU
--   rw [←UU_stable]
--   apply goodVAR0
--   apply goodUU
--   apply goodEL
--   rw [UU_stable]
--   apply goodSUCC
--   apply goodUU
--   rw [UU_stable]
--   apply goodSUCC
--   apply goodUU
--   rw [←UU_stable]
--   rw [←UU_stable]
--   apply goodVAR0
--   apply goodUU
--   exact good_pointed





-- mutual
--   -- def SubstArrTy : Ty → Tm → Nat → Ty
--   -- def SubstArrTm : Tm → Tm → Nat → Tm
--   -- def WkArrTy : Ty → Nat → Ty
--   -- | UU, _ => UU
--   -- | EL X, a => EL (WkArrTm X a)
--   -- | PI X Y, a => PI (WkArrTm X a) (WkArrTy Y (succ a))
--   -- | EQ A t t', a => EQ (WkArrTm A a) (WkArrTm t a) (WkArrTm t' a)
--   -- def WkArrTm : Tm → Nat → Tm
--   -- | VAR n, a => if n ≥ a then VAR (succ n) else VAR n
--   -- | APP X Y f t, a => APP (WkArrTm X a) (WkArrTy Y (succ a)) (WkArrTm f a) (WkArrTm t a)
--   -- | TRANSP X s s' Y eq t, a => TRANSP (WkArrTm X a) (WkArrTm s a) (WkArrTm s' a) (WkArrTy Y a) (WkArrTm eq a) (WkArrTm t a)
--   -- def goodWkArrTy {Γ : Con} : (A : Ty) → (a : Nat) → (h : a < Γ.length) → goodTy Γ A →

--   -- def goodUntrunc {Γ : Con} (A : Ty) (z : Tm) : (a : Nat) → (h : a < Γ.length) → goodTm (trunc Γ a h) (Γ[a]'h) z → goodTm Γ (WknTy )

--   def goodSubstArrTy  {Γ : Con} : (A : Ty) → (z : Tm) → (a : Nat) → (h : a < Γ.length) → goodTy Γ A → goodTm (trunc Γ a h) (Γ[a]'h) z → goodTy (substAt Γ z a h) (SubstArrTy A z a)
--   | UU, _,_,_,_,_ => goodUU
--   | EL X,z,a,h,goodEL gX,gz => goodEL (goodSubstArrTm X z a h goodUU gX gz)
--   | EQ X t t',z,a,h,goodEQ gX gt gt',gz => goodEQ (goodSubstArrTm X z a h goodUU gX gz) (goodSubstArrTm t z a h (goodEL gX) gt gz) (goodSubstArrTm t' z a h (goodEL gX) gt' gz)
--   | PI X Y, z,a,h,goodPI gX gY,gz => goodPI (goodSubstArrTm X z a h goodUU gX gz) (@goodSubstArrTy (EL X :: Γ) Y z (succ a) (succ_lt_succ h) gY gz)

--   def goodSubstArrTm {Γ : Con}{A : Ty} : (t : Tm) → (z : Tm) → (a : Nat) → (h : a < Γ.length) → goodTy Γ A → goodTm Γ A t → goodTm (trunc Γ a h) (Γ[a]'h) z → goodTm (substAt Γ z a h) (SubstArrTy A z a) (SubstArrTm t z a)
--   | APP X Y f t, z, a, h, _ , goodAPP gX gY gf gt,gz =>
--         goodSubstArrTm _ _ _ _ (@goodSubstArrTy (EL X::Γ) Y t 0 (zero_lt_succ Γ.length) gY gt) (goodAPP gX gY gf gt) gz
--   | TRANSP X s s' Y eq t, z, a, h, _, goodTRANSP gX gs gs' gY geq gt,gz =>
--         goodSubstArrTm _ _ _ _ (@goodSubstArrTy (EL X::Γ) Y s' 0 (zero_lt_succ Γ.length) gY gs') (goodTRANSP gX gs gs' gY geq gt) gz
--   | VAR m, z, a, h, gw, gv,gz =>
--     if m < a then _ else
--     if m = a then _ else
--     _
-- end

-- def goodSubst {Γ : Con}{X : Tm}{s : Tm}{Y : Ty} (gs : goodTm Γ (EL X) s) (gY : goodTy (EL X::Γ) Y) : goodTy Γ (SubstTy Y s) :=
--         @goodSubstArrTy (EL X :: Γ) Y s 0 (zero_lt_succ Γ.length) gY gs

-- def extractGoodVar {Γ : Con}{A : Ty}{n : Nat} : goodTm Γ A (VAR n) →
--   ∃ (h : n < Γ.length), A = WknTy Γ n h := sorry
universe u v w

structure indData where
    (Con_D : Con → Type u)
    (Ty_D : (Γ : Con) → Con_D Γ → Ty → Type v)
    (Tm_D : (Γ : Con) → (Γ_D : Con_D Γ) → (A : Ty) → Ty_D Γ Γ_D A → Tm → Type w)
    (nil_D : Con_D [])
    (cons_D : (Γ : Con) → (Γ_D : Con_D Γ) → (A : Ty) → (A_D : Ty_D Γ Γ_D A) → Con_D (A::Γ))
    -- (WkTy_D : (Γ : Con) → (Γ_D : Con_D Γ) →
    --           (A : Ty) → (A_D : Ty_D Γ Γ_D A) →
    --           (A' : Ty) → (A'_D : Ty_D Γ Γ_D A') →
    --           Ty_D (A'::Γ) (cons_D Γ Γ_D A' A'_D) (WkTy A))
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
    -- (VAR_D :(Γ : Con) → (Γ_D : Con_D Γ) →
    --         (n : Nat) → (h : n < List.length Γ) →
    --         (A_D : Ty_D Γ Γ_D (WknTy Γ n h)) →
    --         Tm_D Γ Γ_D (WknTy Γ n h) A_D (VAR n))
    (VAR0_D : (Γ : Con) → (Γ_D : Con_D Γ) →
            (A : Ty) → (A_D : Ty_D Γ Γ_D A) → (A'_D : Ty_D (A::Γ) (cons_D Γ Γ_D A A_D) (WkTy A)) →
            Tm_D (A::Γ) (cons_D Γ Γ_D A A_D) (WkTy A) A'_D (VAR 0)
            )
    (VARSUCC_D : (Γ : Con) → (Γ_D : Con_D Γ) →
            (A : Ty) → (A_D : Ty_D Γ Γ_D A) →
            (t : Tm) → Tm_D Γ Γ_D A A_D t →
            (A' : Ty) → (A'_D : Ty_D Γ Γ_D A') →
            (WkA_D : Ty_D (A'::Γ) (cons_D Γ Γ_D A' A'_D) (WkTy A)) →
            Tm_D (A'::Γ) (cons_D Γ Γ_D A' A'_D) (WkTy A) WkA_D (WkTm t))
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


-- def VAR0_D {P : indData}

inductive Arg : Type where
| Impl : String → Ty → Arg
| Expl : String → Ty → Arg
| Anon : Ty → Arg
open Arg

def getName : Arg → Option String
| Impl i _ => some i
| Expl i _ => some i
| Anon _ => none


structure GATdata where
  (con : Con)
  (topnames : List String)
  (telescopes : List (List Arg × Ty))

structure GAT extends GATdata where
  (elim : (P : indData) → P.Con_D con)

-- #check Listappend
def GAT.subnames (𝔊 : GAT) : List String :=
  List.join $
  List.map (λ (L,s) => L ++ [s]) $
  List.zip
    (List.map ((mappartial getName) ∘ Prod.fst) (𝔊.telescopes))
    (𝔊.topnames)

-- mutual
--     def elim (P : indData) : (Γ : Con) → goodCon Γ → P.Con_D Γ
--     | [],_ => P.nil_D
--     | A::Γ,goodCons gA gΓ => P.cons_D _ (elim _ _ gΓ) _ (elimTy _ _ _ _ gΓ gA)

--     -- def dispGetElem (P : indData) (Γ : Con) (n : Nat) (h : n < List.length Γ) :
--     --     Σ (Γ_D : P.Con_D Γ), P.Ty_D Γ Γ_D (WknTy Γ n h) :=  ⟨elim _ _,elimTy _ _ _ _ _⟩

--     -- def dispWknTy : (P : indData) →
--     --     (Γ : Con) → (Γ_D : P.Con_D Γ) →
--     --     (A : Ty) → (A_D : P.Ty_D Γ Γ_D A) →
--     --     (n : Nat) → (h : n < List.length Γ) →
--     --     P.Ty_D Γ Γ_D (WknTy Γ n h) →
--     --     P.Ty_D (A::Γ) (P.cons_D _ Γ_D _ A_D) (WknTy (A::Γ) (succ n) (succ_lt_succ h)) := _
--     def elimWknTy {P : indData} : (Γ : Con) → (Γ_D : P.Con_D Γ) → (n : Nat) → (h : n < Γ.length) → P.Ty_D Γ Γ_D (WknTy Γ n h)
--     | A::Γ , _ , 0 , _ => _

--     def elimTy (P : indData) (Γ : Con) (Γ_D : P.Con_D Γ) : (A : Ty) → goodCon Γ → goodTy Γ A → P.Ty_D Γ Γ_D A
--     | UU,_,goodUU => P.UU_D Γ Γ_D
--     | EL X,gΓ,goodEL gX => P.EL_D _ _ _ (elimTm _ _ _ _ _ _ gΓ goodUU gX)
--     | PI X Y,gΓ,goodPI gX gY => P.PI_D _ _ _ (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTy _ _ _ _ (goodCons (goodEL gX) gΓ) gY)
--     | EQ X s s',gΓ,goodEQ gX gs gs' => P.EQ_D _ _ _ (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs')

--     def elimTm (P : indData) (Γ : Con) (Γ_D : P.Con_D Γ) : (A : Ty) → (A_D : P.Ty_D Γ Γ_D A) → (t : Tm) → goodCon Γ → goodTy Γ A → goodTm Γ A t → P.Tm_D Γ Γ_D A A_D t
--     | _,_,APP X Y f t,gΓ,_, @goodAPP _ _ _ _ _ gX gY gf gt => P.APP_D Γ Γ_D X (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTy _ _ _ _ (goodCons (goodEL gX) gΓ) gY) _ (elimTm _ _ _ _ _ _ gΓ (goodPI gX gY) gf) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gt) _
--     | _,_,TRANSP X s s' Y eq k,gΓ,_,goodTRANSP gX gs gs' gY geq gk => P.TRANSP_D Γ Γ_D _ (elimTm _ _ _ _ _ _ gΓ goodUU gX) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs) _ (elimTm _ _ _ _ _ _ gΓ (goodEL gX) gs') _ (elimTy _ _ _ _ (goodCons (goodEL gX) gΓ) gY) (elimTy _ _ _ _ gΓ (goodSubst gs gY)) _ _ (elimTm _ _ _ _ _ _ gΓ (goodEQ gX gs gs') geq) _ (elimTm _ _ _ _ (elimTy _ _ _ _ _ _) _ gΓ (goodSubst gs gY) gk)
--     | A,_,VAR n, gΓ,gA, gv => by
--         let hh := @extractGoodVar _ _ _ gv
--         let h := hh.1
--         let p : A = WknTy Γ n h := hh.2
--         rw [p]

--         -- rw p

--       -- P.VAR_D Γ Γ_D n h (elimWknTy Γ Γ_D n h)
-- end

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
