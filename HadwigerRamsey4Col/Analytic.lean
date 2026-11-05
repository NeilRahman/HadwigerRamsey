import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open Real
open scoped BigOperators
namespace HadwigerRamsey4Col

noncomputable def cost (q : ℝ) : ℝ := -log (1-q)
noncomputable def tStar (p : ℝ) : ℝ := -(3/4 : ℝ)*log p

theorem cost_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) : 0 ≤ cost q := by
  exact neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))

lemma cost_tangent {q r : ℝ} (hq : q < 1) (hr : r < 1) :
    cost r + (q-r)/(1-r) ≤ cost q := by
  have h := log_le_sub_one_of_pos (div_pos (sub_pos.mpr hq) (sub_pos.mpr hr))
  rw [log_div (by linarith : 1-q ≠ 0) (by linarith : 1-r ≠ 0)] at h
  dsimp [cost]
  have he : (1-q)/(1-r)-1 = -(q-r)/(1-r) := by field_simp [ne_of_gt (sub_pos.mpr hr)]; ring
  rw [he, neg_div] at h
  linarith

lemma cost_third : cost (1/3) = log (3/2) := by
  dsimp [cost]
  rw [← log_inv]
  norm_num

lemma cost_two_thirds : cost (2/3) = log (3/2) + log 2 := by
  dsimp [cost]
  rw [← log_inv, ← log_mul (by norm_num : (3/2 : ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  norm_num

lemma two_cost_bound {q r : ℝ} (hq : q < 1) (hr : r < 1) (hs : q+r=1) :
    (3/2 : ℝ)*log (3/2)+(1/2 : ℝ)*log 2 ≤ cost q + (1/2 : ℝ)*cost r := by
  have h0 := cost_tangent hq (show (1/3:ℝ)<1 by norm_num)
  have h1 := cost_tangent hr (show (2/3:ℝ)<1 by norm_num)
  rw [cost_third] at h0
  rw [cost_two_thirds] at h1
  norm_num at h0 h1
  linarith

lemma log_lower_bounds : (81/200 : ℝ) < log (3/2) ∧ (69/100 : ℝ) < log 2 := by
  have h0 := sum_range_le_log_div (x := (1/5 : ℝ)) (by norm_num) (by norm_num) 2
  have h1 := sum_range_le_log_div (x := (1/3 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h0 h1
  constructor <;> linarith

lemma tStar_lt_threshold {p : ℝ} (hp : 0 < p) (hpoly : 3*p^6+2*p-2=0) :
    tStar p < (2213/10000 : ℝ) := by
  have hp0 : (1489/2000 : ℝ) < p := by
    by_contra hn
    have hle : p ≤ (1489/2000 : ℝ) := le_of_not_gt hn
    have hpow := pow_le_pow_left₀ hp.le hle 6
    nlinarith
  have hl := log_lt_log (by norm_num : (0:ℝ)<1489/2000) hp0
  have he : log (1489/2000 : ℝ) = -log (2000/1489 : ℝ) := by
    rw [← log_inv]
    norm_num
  rw [he] at hl
  have hb := log_div_le_sum_range_add (x := (511/3489 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hb
  dsimp [tStar]
  linarith

end HadwigerRamsey4Col
