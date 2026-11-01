import HadwigerRamsey.FOpt.Definitions
import HadwigerRamsey.FOpt
import HadwigerRamsey.Opt

namespace HadwigerRamsey.Existence
open Real
noncomputable def p : ℝ := 5-2*sqrt 6
lemma p_bounds : 0 < p ∧ p < 1/3 := by
  have h : 2*p = FOpt.q := by dsimp [p,FOpt.q]; ring
  constructor <;> linarith [FOpt.q_bounds.1,FOpt.q_bounds.2]
lemma beta_positive : 0 < beta := HadwigerRamsey.beta_pos
lemma sqrt_internal : sqrt (-log (2*p)) = 2*beta := by
  have h : 2*p = FOpt.q := by dsimp [p,FOpt.q]; ring
  rw [h]; dsimp [beta,FOpt.beta]; ring
lemma entropy_mixed : -(1/2:ℝ)*log (1-p)-(1/2:ℝ)*log (1/2:ℝ) = beta^2 := by
  have h := FOpt.log_half_identity
  rw [FOpt.exp_neg_four_c] at h
  have hq : 2-FOpt.q = 2*(1-p) := by dsimp [p,FOpt.q]; ring
  rw [hq,log_mul (by norm_num) (by linarith [p_bounds.2] : (1-p) ≠ 0)] at h
  rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,log_inv]
  change _ = FOpt.beta^2
  rw [FOpt.beta_sq]
  dsimp only [FOpt.F] at h
  linarith only [h]
end HadwigerRamsey.Existence
