import HadwigerRamsey.ThomasonUpper.ReservoirAsymptotic

open scoped Topology
open Real Filter

namespace HadwigerRamsey.ThomasonUpper

/-- All errors from capping and deleting the two reservoirs can be made
uniformly small, before the graph and its vertex classes are chosen. -/
theorem eventually_final_error_bounds {epsilon d e : ℝ}
    (hepsilon : 0 < epsilon) (hd : 0 < d) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ log (n : ℝ) ∧
      0 ≤ 4/log (log (n : ℝ)) ∧ 4/log (log (n : ℝ)) ≤ d ∧
      4/(epsilon^3*(n : ℝ)^2) ≤ e := by
  have hll := (tendsto_log_atTop.comp (tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop)).eventually_ge_atTop (max 1 (4/d))
  have hl := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (max 1 (4/(epsilon^3*e)))
  filter_upwards [hll,hl,hn] with n hll hl hn
  change max 1 (4/d) ≤ log (log (n : ℝ)) at hll
  change 1 ≤ log (n : ℝ) at hl
  change max 1 (4/(epsilon^3*e)) ≤ (n : ℝ) at hn
  have hllp : 0 < log (log (n : ℝ)) := by linarith [le_max_left 1 (4/d)]
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans hn
  have hnp : (0 : ℝ) < n := by linarith
  refine ⟨hl,by positivity,?_,?_⟩
  · apply (div_le_iff₀ hllp).mpr
    have hh := (div_le_iff₀ hd).mp ((le_max_right 1 (4/d)).trans hll)
    nlinarith only [hh]
  · apply (div_le_iff₀ (mul_pos (pow_pos hepsilon 3) (sq_pos_of_pos hnp))).mpr
    have hh := (div_le_iff₀ (mul_pos (pow_pos hepsilon 3) he)).mp ((le_max_right 1 (4/(epsilon^3*e))).trans hn)
    have hh' : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith only [hn1]
    have hh'' := mul_le_mul_of_nonneg_left hh' (mul_nonneg (pow_nonneg hepsilon.le 3) he.le)
    nlinarith only [hh,hh'']

end HadwigerRamsey.ThomasonUpper
