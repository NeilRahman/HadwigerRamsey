import HadwigerRamsey4Col.Lemma6
import Mathlib.Analysis.Complex.ExponentialBounds

open Real
namespace HadwigerRamsey4Col

noncomputable abbrev threshold : ℝ := 2213/10000
noncomputable abbrev thresholdPolynomial : ℝ := threshold-threshold^2/2+threshold^3/6
noncomputable def ballA : ℝ := 2*log 2
noncomputable def ballB : ℝ := 3*log (3/2)
noncomputable def ballC : ℝ := 4*log (4/3)
noncomputable def ballK : ℝ := (413/500 : ℝ)*sqrt threshold

lemma threshold_sqrt_bounds : (47/100 : ℝ) < sqrt threshold ∧ sqrt threshold < 941/2000 := by
  have hs := sq_sqrt (show (0:ℝ) ≤ threshold by norm_num)
  have hn := sqrt_nonneg threshold
  constructor <;> norm_num [threshold] at * <;> nlinarith

lemma threshold_capacity_one : capacityF threshold 1 < thresholdPolynomial := by
  have hu := exp_bound' (x := threshold) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, threshold] at hu
  have he := exp_pos threshold
  have hi := inv_pos.mpr he
  have hid := mul_inv_cancel₀ (ne_of_gt he)
  have hp : (1-thresholdPolynomial)*exp threshold < 1 := by norm_num [thresholdPolynomial, threshold] at *; linarith
  have hm := mul_pos (show 0 < 1-(1-thresholdPolynomial)*exp threshold by linarith) hi
  dsimp [capacityF]
  norm_num only [one_pow, div_one, one_mul]
  rw [exp_neg]
  nlinarith

lemma threshold_capacity_small :
    capacityF threshold (17/50 : ℝ) < (13/15 : ℝ)*(17/50 : ℝ)^2 := by
  have he1 := exp_one_lt_d9
  have he0 := exp_pos 1
  have he2 : exp (2:ℝ) < (15/2 : ℝ) := by
    have he : exp (2:ℝ)=(exp (1:ℝ))^2 := by rw [pow_two, ← exp_add]; norm_num
    rw [he]
    nlinarith
  have ht : threshold/(17/50 : ℝ)^2 < 2 := by norm_num
  have hu := (exp_lt_exp.mpr ht).trans he2
  have he := exp_pos (threshold/(17/50 : ℝ)^2)
  have hi := inv_pos.mpr he
  have hid := mul_inv_cancel₀ (ne_of_gt he)
  have hm := mul_pos (sub_pos.mpr hu) hi
  dsimp [capacityF]
  rw [exp_neg]
  nlinarith

lemma fixed_capacity_sum_lt :
    2*capacityF threshold 1+(32/25 : ℝ)*sqrt threshold < 1 := by
  have hF := threshold_capacity_one
  have hs := threshold_sqrt_bounds.2
  norm_num [thresholdPolynomial, threshold] at *
  linarith

lemma ball_capacity_sum_lt :
    3*capacityF threshold 1+capacityF threshold (17/50 : ℝ)+
      (16/25 : ℝ)*sqrt threshold < 1 := by
  have hF := threshold_capacity_one
  have hG := threshold_capacity_small
  have hs := threshold_sqrt_bounds.2
  norm_num [thresholdPolynomial, threshold] at *
  linarith

lemma ball_log_bounds : (6931/10000 : ℝ) < log 2 ∧ log 2 < 347/500 ∧
    (2027/5000 : ℝ) < log (3/2) ∧ log (3/2 : ℝ) < 811/2000 ∧
    (719/2500 : ℝ) < log (4/3) := by
  have h0 := sum_range_le_log_div (x := (1/3 : ℝ)) (by norm_num) (by norm_num) 4
  have h1 := log_div_le_sum_range_add (x := (1/3 : ℝ)) (by norm_num) (by norm_num) 4
  have h2 := sum_range_le_log_div (x := (1/5 : ℝ)) (by norm_num) (by norm_num) 3
  have h3 := log_div_le_sum_range_add (x := (1/5 : ℝ)) (by norm_num) (by norm_num) 3
  have h4 := sum_range_le_log_div (x := (1/7 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma ball_constants : 0 < ballA-ballB ∧ 0 < ballA-2*ballB+ballC ∧
    2*(ballA-ballB) < ballK ∧
    (17/50 : ℝ)*ballA+(33/50 : ℝ)*ballB > ballK+4*threshold := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ball_log_bounds
  obtain ⟨hs0,hs1⟩ := threshold_sqrt_bounds
  dsimp [ballA,ballB,ballC,ballK]
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  norm_num [threshold] at *
  linarith

end HadwigerRamsey4Col
