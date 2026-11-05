import HadwigerRamsey4Col.Entropy

open Real
namespace HadwigerRamsey4Col

lemma coefficient_log_bounds :
    (152/375 : ℝ) < log (3/2) ∧ (511/480 : ℝ) < log (32/11) ∧
    log (43/32 : ℝ) < 3/10 ∧ log (8/3 : ℝ) < 1 := by
  have h0 := sum_range_le_log_div (x := (1/5 : ℝ)) (by norm_num) (by norm_num) 3
  have h1 := sum_range_le_log_div (x := (21/43 : ℝ)) (by norm_num) (by norm_num) 4
  have h2 := log_div_le_sum_range_add (x := (11/75 : ℝ)) (by norm_num) (by norm_num) 3
  have h3 := log_div_le_sum_range_add (x := (5/11 : ℝ)) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma alpha_coefficient_bound : (5/4 : ℝ) < alphaCoefficient := by
  obtain ⟨hw0,hw1⟩ := weight_bounds
  obtain ⟨hb,hl,hu,_⟩ := coefficient_log_bounds
  have hw : 0 < weight := by linarith
  have hwplus : 0 < 1+weight := by linarith
  have hlw : log weight < -(511/480 : ℝ) := by
    have h := log_lt_log hw hw1
    have he : log (11/32 : ℝ) = -log (32/11 : ℝ) := by
      rw [← log_inv]
      norm_num
    rw [he] at h
    linarith
  have hlp : log (1+weight) < (3/10 : ℝ) := by
    have h := log_lt_log hwplus (show 1+weight < (43/32 : ℝ) by linarith)
    linarith
  have hb' := mul_le_mul_of_nonneg_left hb.le (show 0 ≤ 3*weight-1/4 by linarith)
  have hl' := mul_le_mul_of_nonneg_left hlw.le (show 0 ≤ (5/4 : ℝ)-weight by linarith)
  have hu' := mul_le_mul_of_nonneg_left hlp.le (show 0 ≤ weight-1/4 by linarith)
  dsimp [alphaCoefficient, shiftedWeight, entropy, entropySlope]
  rw [log_div (ne_of_gt hwplus) (ne_of_gt hw)]
  nlinarith

lemma gamma_coefficient_bound : (-1 : ℝ) < gammaCoefficient := by
  obtain ⟨hw0,hw1⟩ := weight_bounds
  have hw : 0 < weight := by linarith
  have hr0 : 0 < 2*(1+weight)/(3*weight) := by positivity
  have hr : 2*(1+weight)/(3*weight) < (8/3 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 3*weight)).mpr
    linarith
  have hl := log_lt_log hr0 hr
  have hb := coefficient_log_bounds.2.2.2
  have he : gammaCoefficient = -log (2*(1+weight)/(3*weight)) := by
    dsimp [gammaCoefficient, entropySlope]
    rw [log_div (by positivity : 2*(1+weight) ≠ 0) (by positivity : 3*weight ≠ 0)]
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : 1+weight ≠ 0)]
    rw [log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt hw)]
    rw [log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      log_div (by positivity : 1+weight ≠ 0) (ne_of_gt hw)]
    ring
  rw [he]
  linarith

end HadwigerRamsey4Col
