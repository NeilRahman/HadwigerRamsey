import HadwigerRamsey.FOpt.Calculus
import HadwigerRamsey.FOpt.Constants
import HadwigerRamsey.FOpt.Coverage

set_option maxHeartbeats 1000000

namespace HadwigerRamsey.FOpt
open Real Set LeanCert.Core LeanCert.Core.IntervalRat

noncomputable def realEnv (x : ℝ) : ℕ → ℝ
  | 0 => x
  | 1 => c
  | 2 => F
  | 3 => a
  | _ => 0

lemma env_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    ∀ i, realEnv x i ∈ certificateEnv I i := by
  intro i
  rcases i with _ | i
  · exact hx
  rcases i with _ | i
  · exact c_mem
  rcases i with _ | i
  · exact F_mem
  rcases i with _ | i
  · exact a_mem
  · simpa only [realEnv,certificateEnv,Rat.cast_zero] using IntervalRat.mem_singleton 0

lemma gapE_real (x : ℝ) : gapE.real (realEnv x) = gap x := by
  change F*x + a*x*(x-((1/2 : ℚ) : ℝ))*(((1 : ℚ) : ℝ)-x) -
    x*x*log (((2 : ℚ) : ℝ)-exp (-(c/(x*x)))) = _
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  simp only [gap,cubic,value,pow_two]

lemma curvatureE_real (x : ℝ) : curvatureE.real (realEnv x) = a*(3-6*x)-second c x := by
  change a*(3-6*x) - (2*log (2-exp (-(c/(x*x)))) -
    2*(c/(x*x))*exp (-(c/(x*x)))/(2-exp (-(c/(x*x)))) -
    8*(c/(x*x))*(c/(x*x))*exp (-(c/(x*x)))/
      ((2-exp (-(c/(x*x))))*(2-exp (-(c/(x*x)))))) = _
  simp only [second,pow_two]
  ring

lemma in_cell {x : ℝ} (hx : 0 ≤ x) : x ∈ cell ⌊1000*x⌋₊ := by
  have hl := Nat.floor_le (by positivity : 0 ≤ 1000*x)
  have hu := Nat.lt_floor_add_one (1000*x)
  change ((cell ⌊1000*x⌋₊).lo : ℝ) ≤ x ∧ x ≤ ((cell ⌊1000*x⌋₊).hi : ℝ)
  simp only [cell,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_add,Rat.cast_one]
  constructor <;> linarith

lemma gap_nonneg_outer {x : ℝ}
    (hx : 350/1000 ≤ x ∧ x < 400/1000 ∨ 600/1000 ≤ x ∧ x ≤ 1) : 0 ≤ gap x := by
  have hx0 : 0 ≤ x := by rcases hx with h | h <;> linarith [h.1]
  let j := ⌊1000*x⌋₊
  have hj : j < 1001 := by
    have h1 : x ≤ 1 := by rcases hx with h | h <;> linarith [h.2]
    have := Nat.floor_le_of_le (show 1000*x ≤ (1000 : ℕ) by norm_num; linarith)
    omega
  have hr : 350 ≤ j ∧ j ≤ 399 ∨ 600 ≤ j := by
    rcases hx with h | h
    · left
      constructor
      · exact Nat.le_floor (by norm_num; linarith [h.1])
      · have := (Nat.floor_lt (by positivity : 0 ≤ 1000*x)).mpr (show 1000*x < (400 : ℕ) by norm_num; linarith [h.2])
        omega
    · right
      exact Nat.le_floor (by norm_num; linarith [h.1])
  have hh := RExpr.lowerCheck_sound gapE _ (realEnv x) (env_mem (in_cell hx0)) 16 0
    (gap_checks ⟨j,hj⟩ hr)
  simpa only [Rat.cast_zero,gapE_real] using hh

lemma curvature_nonneg {x : ℝ} (hx : x ∈ Icc (400/1000 : ℝ) (600/1000)) :
    0 ≤ a*(3-6*x)-second c x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  let j := ⌊1000*x⌋₊
  have hj : j < 601 := by
    have := Nat.floor_le_of_le (show 1000*x ≤ (600 : ℕ) by norm_num; linarith [hx.2])
    omega
  have hr : 400 ≤ j := Nat.le_floor (by norm_num; linarith [hx.1])
  have hh := RExpr.lowerCheck_sound curvatureE _ (realEnv x) (env_mem (in_cell hx0)) 16 0
    (curvature_checks ⟨j,hj⟩ hr)
  simpa only [Rat.cast_zero,curvatureE_real] using hh

lemma gap_nonneg_middle {x : ℝ} (hx : x ∈ Icc (400/1000 : ℝ) (600/1000)) : 0 ≤ gap x := by
  have hzero : ∀ y ∈ Icc (400/1000 : ℝ) (600/1000), y ≠ 0 := by
    intro y hy; linarith [hy.1]
  have hc : ConvexOn ℝ (Icc (400/1000 : ℝ) (600/1000)) gap :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun y hy => (hasDerivAt_gap (hzero y hy)).continuousAt.continuousWithinAt)
      (fun y hy => (hasDerivAt_gap (hzero y (interior_subset hy))).hasDerivWithinAt)
      (fun y hy => (hasDerivAt_gapFirst (hzero y (interior_subset hy))).hasDerivWithinAt)
      (fun y hy => curvature_nonneg (interior_subset hy))
  have hhalf : (1/2 : ℝ) ∈ interior (Icc (400/1000 : ℝ) (600/1000)) := by
    rw [interior_Icc]; constructor <;> norm_num
  have hd : derivWithin gap (Ioi (1/2)) (1/2) = 0 := by
    rw [(hasDerivAt_gap (by norm_num : (1/2 : ℝ) ≠ 0)).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi _),gapFirst_half]
  have hm := hc.isMinOn_of_rightDeriv_eq_zero hhalf hd hx
  change gap (1/2) ≤ gap x at hm
  simpa only [gap_half] using hm

lemma gap_nonneg_small {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (350/1000)) : 0 ≤ gap x := by
  have hlog : log (2-exp (-(c/x^2))) ≤ log 2 :=
    log_le_log (log_argument_pos c_pos.le) (by linarith [exp_pos (-(c/x^2))])
  have hf : value c x ≤ x^2*log 2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg x)
  have hF : 293325/1000000 ≤ F := by simpa [fI] using F_mem.1
  have ha0 : 4544/10000 ≤ a := by simpa [aI] using a_mem.1
  have ha1 : a ≤ 4545/10000 := by simpa [aI] using a_mem.2
  have hlog2 : log 2 ≤ 693148/1000000 := by simpa [log2I] using log2_mem.2
  have hprod : 0 ≤ x*(1/2-x)*(1-x) := mul_nonneg (mul_nonneg hx.1 (by linarith [hx.2])) (by linarith [hx.2])
  have hp : cubic F a x ≥ 293325/1000000*x - (4545/10000)*(x*(1/2-x)*(1-x)) := by
    have h1 := mul_le_mul_of_nonneg_right hF hx.1
    have h2 := mul_le_mul_of_nonneg_right ha1 hprod
    dsimp [cubic]; nlinarith only [h1,h2]
  have h2 : x^2*log 2 ≤ x^2*(693148/1000000) := mul_le_mul_of_nonneg_left hlog2 (sq_nonneg x)
  have ht : (0 : ℝ) ≤ x*(350/1000-x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have ht2 := mul_nonneg hx.1 ht
  have ht3 : (0 : ℝ) ≤ x^3 := pow_nonneg hx.1 3
  dsimp [gap]
  nlinarith [sq_nonneg x]

lemma cubic_envelope {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : value c x ≤ cubic F a x := by
  have : 0 ≤ gap x := by
    by_cases hs : x ≤ 350/1000
    · exact gap_nonneg_small ⟨hx.1,hs⟩
    by_cases hm : x < 400/1000
    · exact gap_nonneg_outer (Or.inl ⟨by linarith,hm⟩)
    by_cases hm2 : x ≤ 600/1000
    · exact gap_nonneg_middle ⟨by linarith,hm2⟩
    · exact gap_nonneg_outer (Or.inr ⟨by linarith,hx.2⟩)
  exact sub_nonneg.mp this

end HadwigerRamsey.FOpt
