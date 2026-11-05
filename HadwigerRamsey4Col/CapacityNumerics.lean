import HadwigerRamsey4Col.Analytic

open Real
namespace HadwigerRamsey4Col

lemma exp_first_anchor : (3507/1000 : ℝ) < exp (251/200 : ℝ) ∧
    exp (251/200 : ℝ) < 3509/1000 := by
  have hl := sum_le_exp_of_nonneg (x := (251/400 : ℝ)) (by norm_num) 10
  have hu := exp_bound' (x := (251/400 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ] at hl hu
  have hp := exp_pos (251/400 : ℝ)
  have he : exp (251/200 : ℝ) = (exp (251/400 : ℝ))^2 := by
    rw [pow_two, ← exp_add]
    norm_num
  rw [he]
  constructor <;> nlinarith

lemma exp_second_anchor : (2787/1000 : ℝ) < exp (41/40 : ℝ) ∧
    exp (41/40 : ℝ) < 27871/10000 := by
  have hl := sum_le_exp_of_nonneg (x := (41/80 : ℝ)) (by norm_num) 10
  have hu := exp_bound' (x := (41/80 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ] at hl hu
  have hp := exp_pos (41/80 : ℝ)
  have he : exp (41/40 : ℝ) = (exp (41/80 : ℝ))^2 := by
    rw [pow_two, ← exp_add]
    norm_num
  rw [he]
  constructor <;> nlinarith

lemma log_second_anchor_bound : log (73613/55742 : ℝ) < (1391/5000 : ℝ) := by
  have h := log_div_le_sum_range_add (x := (17871/129355 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

end HadwigerRamsey4Col
