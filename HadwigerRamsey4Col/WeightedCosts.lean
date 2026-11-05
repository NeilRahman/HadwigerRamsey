import HadwigerRamsey4Col.Entropy

open Real
namespace HadwigerRamsey4Col

/-- The weighted two-colour inequality preceding Proposition 5. -/
theorem weighted_two_colour_cost {u q r : ℝ} (hu : 0 < u)
    (hq : q < 1) (hr : r < 1) (hs : q+r=1) :
    entropy u ≤ cost q+u*cost r := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have hu1 : 0 < 1+u := by linarith
  have htq := log_le_sub_one_of_pos (div_pos (mul_pos hq0 hu1) hu)
  have htr := log_le_sub_one_of_pos (mul_pos hr0 hu1)
  rw [log_div (mul_ne_zero (ne_of_gt hq0) (ne_of_gt hu1)) (ne_of_gt hu),
    log_mul (ne_of_gt hq0) (ne_of_gt hu1)] at htq
  rw [log_mul (ne_of_gt hr0) (ne_of_gt hu1)] at htr
  have hh := mul_le_mul_of_nonneg_left htq hu.le
  have he : u*(q*(1+u)/u-1)=q*(1+u)-u := by field_simp
  rw [he] at hh
  have hlin : (q+r)*(1+u)=1+u := by rw [hs]; ring
  dsimp [entropy, cost]
  rw [show 1-q=r by linarith, show 1-r=q by linarith]
  nlinarith

/-- A tangent bound at a formal diagonal density, which may be negative. -/
lemma weighted_diagonal_cost {u S q : ℝ} (hu : 0 < u) (hS : 0 < S) (hq : q < 1) :
    u*log (S/(2*u))+(S/2)*q-S/2+u ≤ u*cost q := by
  have hr : 1-2*u/S < 1 := by
    have := div_pos (show 0 < 2*u by positivity) hS
    linarith
  have ht := cost_tangent hq hr
  have he : cost (1-2*u/S) = log (S/(2*u)) := by
    dsimp [cost]
    rw [show 1-(1-2*u/S)=2*u/S by ring, ← log_inv, inv_div]
  rw [he] at ht
  have h := mul_le_mul_of_nonneg_left ht hu.le
  rw [mul_add] at h
  have hrat : u*((q-(1-2*u/S))/(1-(1-2*u/S))) = S/2*q-S/2+u := by
    field_simp [ne_of_gt hu, ne_of_gt hS]
    ring
  rw [hrat] at h
  linarith

lemma cost_ge_self {q : ℝ} (hq : q < 1) : q ≤ cost q := by
  have h := cost_tangent hq (show (0:ℝ)<1 by norm_num)
  norm_num [cost] at h
  exact h

end HadwigerRamsey4Col
