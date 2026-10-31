import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Tactic

namespace HadwigerRamsey.FOpt
open LeanCert.Core LeanCert.Core.IntervalRat

/-- Outward rounding limits the size of exact rational certificates. -/
def roundInterval (I : IntervalRat) : IntervalRat where
  lo := ((⌊I.lo*1000000000⌋ : ℤ) : ℚ) / 1000000000
  hi := ((⌈I.hi*1000000000⌉ : ℤ) : ℚ) / 1000000000
  le := by
    have h1 := Int.floor_le (I.lo*1000000000)
    have h2 := Int.le_ceil (I.hi*1000000000)
    have h3 := I.le
    linarith

lemma mem_roundInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : x ∈ roundInterval I := by
  have hl : ((⌊I.lo*1000000000⌋ : ℤ) : ℚ)/1000000000 ≤ I.lo := by
    have := Int.floor_le (I.lo*1000000000); linarith
  have hu : I.hi ≤ ((⌈I.hi*1000000000⌉ : ℤ) : ℚ)/1000000000 := by
    have := Int.le_ceil (I.hi*1000000000); linarith
  change ((roundInterval I).lo : ℝ) ≤ x ∧ x ≤ ((roundInterval I).hi : ℝ)
  dsimp only [roundInterval]
  constructor
  · exact le_trans (by exact_mod_cast hl) hx.1
  · exact le_trans hx.2 (by exact_mod_cast hu)

/-- The elementary expressions used by the finite numerical certificates. -/
inductive RExpr where
  | const : ℚ → RExpr
  | var : ℕ → RExpr
  | add : RExpr → RExpr → RExpr
  | mul : RExpr → RExpr → RExpr
  | neg : RExpr → RExpr
  | inv : RExpr → RExpr
  | exp : RExpr → RExpr
  | log : RExpr → RExpr
  deriving Repr

noncomputable def RExpr.real (v : ℕ → ℝ) : RExpr → ℝ
  | .const q => q
  | .var i => v i
  | .add a b => a.real v + b.real v
  | .mul a b => a.real v * b.real v
  | .neg a => -a.real v
  | .inv a => (a.real v)⁻¹
  | .exp a => Real.exp (a.real v)
  | .log a => Real.log (a.real v)

/-- Positive-domain inversion. Invalid domains are rejected, not assigned bounds. -/
def positiveInverse (I : IntervalRat) (h : 0 < I.lo) : IntervalRat :=
  invNonzero ⟨I, by simp only [containsZero]; intro hz; exact (not_le.mpr h) hz.1⟩

def RExpr.bounds (v : ℕ → IntervalRat) (depth : ℕ) : RExpr → Option IntervalRat
  | .const q => some (singleton q)
  | .var i => some (v i)
  | .add a b => do return IntervalRat.add (← a.bounds v depth) (← b.bounds v depth)
  | .mul a b => do return IntervalRat.mul (← a.bounds v depth) (← b.bounds v depth)
  | .neg a => do return IntervalRat.neg (← a.bounds v depth)
  | .inv a => do
    let I ← a.bounds v depth
    if h : 0 < I.lo then some (positiveInverse I h) else none
  | .exp a => do return roundInterval (expComputable (← a.bounds v depth) depth)
  | .log a => do
    let I ← a.bounds v depth
    if 0 < I.lo then some (roundInterval (logComputable I depth)) else none

/-- Soundness connects the computable rational evaluator to actual real functions. -/
theorem RExpr.bounds_sound (e : RExpr) (v : ℕ → IntervalRat) (r : ℕ → ℝ)
    (hr : ∀ i, r i ∈ v i) (depth : ℕ) {I : IntervalRat}
    (h : e.bounds v depth = some I) : e.real r ∈ I := by
  induction e generalizing I with
  | const q =>
    simp only [RExpr.bounds, Option.some.injEq] at h
    subst I
    exact mem_singleton q
  | var i =>
    simp only [RExpr.bounds, Option.some.injEq] at h
    subst I
    exact hr i
  | add a b ia ib =>
    cases ha : a.bounds v depth <;> cases hb : b.bounds v depth <;>
      simp [RExpr.bounds,ha,hb] at h
    subst I
    exact mem_add (ia ha) (ib hb)
  | mul a b ia ib =>
    cases ha : a.bounds v depth <;> cases hb : b.bounds v depth <;>
      simp [RExpr.bounds,ha,hb] at h
    subst I
    exact mem_mul (ia ha) (ib hb)
  | neg a ia =>
    cases ha : a.bounds v depth <;> simp [RExpr.bounds,ha] at h
    subst I
    exact mem_neg (ia ha)
  | exp a ia =>
    cases ha : a.bounds v depth <;> simp [RExpr.bounds,ha] at h
    subst I
    exact mem_roundInterval (mem_expComputable (ia ha) depth)
  | inv a ia =>
    cases ha : a.bounds v depth with
    | none => simp [RExpr.bounds,ha] at h
    | some J =>
      by_cases hJ : 0 < J.lo
      · simp [RExpr.bounds,ha,hJ] at h
        subst I
        have hx : 0 < a.real r := lt_of_lt_of_le (by exact_mod_cast hJ) (ia ha).1
        exact mem_invNonzero (ia ha) (ne_of_gt hx)
      · simp [RExpr.bounds,ha,hJ] at h
  | log a ia =>
    cases ha : a.bounds v depth with
    | none => simp [RExpr.bounds,ha] at h
    | some J =>
      by_cases hJ : 0 < J.lo
      · simp [RExpr.bounds,ha,hJ] at h
        subst I
        exact mem_roundInterval (mem_logComputable (ia ha) hJ depth)
      · simp [RExpr.bounds,ha,hJ] at h

/-- A finite checker for a lower bound. Its proof is checked by ordinary reduction. -/
def RExpr.lowerCheck (e : RExpr) (v : ℕ → IntervalRat) (depth : ℕ) (c : ℚ) : Bool :=
  match e.bounds v depth with
  | none => false
  | some I => decide (c ≤ I.lo)

theorem RExpr.lowerCheck_sound (e : RExpr) (v : ℕ → IntervalRat) (r : ℕ → ℝ)
    (hr : ∀ i, r i ∈ v i) (depth : ℕ) (c : ℚ)
    (h : e.lowerCheck v depth c = true) : (c : ℝ) ≤ e.real r := by
  cases he : e.bounds v depth with
  | none => simp [RExpr.lowerCheck,he] at h
  | some I =>
    have hc : c ≤ I.lo := by simpa [RExpr.lowerCheck,he] using h
    exact le_trans (by exact_mod_cast hc) (e.bounds_sound v r hr depth he).1

end HadwigerRamsey.FOpt
