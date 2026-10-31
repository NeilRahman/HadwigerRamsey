import Mathlib

namespace HadwigerRamsey.FOpt
open Real

noncomputable def q : ℝ := 10 - 4*sqrt 6
noncomputable def beta : ℝ := sqrt (-log q) / 2
noncomputable def c : ℝ := -log q / 4
noncomputable def F : ℝ := log 2 - c
noncomputable def a : ℝ := 4*F - 16*c*q/(2-q)
noncomputable def value (c x : ℝ) : ℝ := x^2 * log (2-exp (-(c/x^2)))
noncomputable def function (x : ℝ) : ℝ := value (beta^2) x

lemma q_bounds : 202041028/1000000000 ≤ q ∧ q ≤ 202041030/1000000000 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hp := Real.sqrt_nonneg (6 : ℝ)
  dsimp [q]
  constructor <;> nlinarith only [h,hp]

lemma q_pos : 0 < q := lt_of_lt_of_le (by norm_num) q_bounds.1
lemma q_lt_one : q < 1 := lt_of_le_of_lt q_bounds.2 (by norm_num)
lemma c_pos : 0 < c := by dsimp [c]; have := log_neg q_pos q_lt_one; linarith
lemma beta_sq : beta^2 = c := by
  have h : 0 ≤ -log q := by have := log_neg q_pos q_lt_one; linarith
  dsimp [beta,c]
  rw [div_pow, sq_sqrt h]
  norm_num

lemma exp_neg_four_c : exp (-4*c) = q := by
  have he : -4*c = log q := by dsimp [c]; ring
  rw [he, exp_log q_pos]

lemma log_half_identity : log (2-exp (-4*c)) = 2*F := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hq : (2-q)^2 = 16*q := by dsimp [q]; nlinarith only [hs]
  have hpos : 0 < 2-q := by linarith [q_lt_one]
  have hlog := congrArg log hq
  rw [log_pow,log_mul (by norm_num) q_pos.ne'] at hlog
  have h4 : log (16 : ℝ) = 4*log 2 := by rw [show (16 : ℝ) = 2^4 by norm_num,log_pow]; norm_num
  rw [h4] at hlog
  norm_num at hlog
  rw [exp_neg_four_c]
  dsimp [F,c]
  linarith only [hlog]

@[simp] lemma value_zero (c : ℝ) : value c 0 = 0 := by simp [value]
lemma value_half : value c (1/2) = F/2 := by
  dsimp [value]
  norm_num
  rw [show -(c / (1/4 : ℝ)) = -4*c by ring,log_half_identity]
  ring

end HadwigerRamsey.FOpt
