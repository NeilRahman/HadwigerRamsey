import HadwigerRamsey4Col.CapacityCalculus
import HadwigerRamsey4Col.CapacityNumerics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Real Set
namespace HadwigerRamsey4Col

lemma first_anchor_head {z : ℝ} (hz : z ∈ Icc 0 (251/200 : ℝ)) :
    exp z ≤ 1+2*z := by
  have hu := exp_first_anchor.2
  have ha : 0 ≤ 1-z/(251/200 : ℝ) := by linarith [hz.2]
  have hb : 0 ≤ z/(251/200 : ℝ) := div_nonneg hz.1 (by norm_num)
  have hh := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ (251/200 : ℝ)) ha hb
    (show 1-z/(251/200 : ℝ)+z/(251/200 : ℝ)=1 by ring)
  norm_num at hh
  have hmul := mul_le_mul_of_nonneg_left hu.le hb
  nlinarith [hz.1]

lemma first_anchor_derivative_bound :
    2*sqrt (251/200 : ℝ)*exp (-(251/200 : ℝ)) ≤ (16/25 : ℝ) := by
  have hs : sqrt (251/200 : ℝ) < (1121/1000 : ℝ) := by
    have := sq_sqrt (show (0:ℝ) ≤ 251/200 by norm_num)
    have := sqrt_nonneg (251/200 : ℝ)
    nlinarith
  have hl := exp_first_anchor.1
  rw [exp_neg]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (exp_pos (251/200 : ℝ))).mpr
  nlinarith

/-- The first normalized capacity inequality. -/
theorem first_normalized_capacity {z : ℝ} (hz : 0 < z) :
    1-exp (-z) ≤ (16/25 : ℝ)*sqrt z := by
  apply capacity_bound_of_anchor (f := fun x => 1-exp (-x)) (C := (16/25 : ℝ)) (a := (251/200 : ℝ)) (df := fun x => exp (-x)) (by norm_num)
  · intro x hx
    have h := ((hasDerivAt_id x).neg.exp).const_sub 1
    exact h.congr_deriv (by simp)
  · intro x hx
    have hh := first_anchor_head hx
    have hh' : 0 ≤ 1+2*x-exp x := by linarith
    have he : (2*x*exp (-x)-(1-exp (-x)))*exp x = 1+2*x-exp x := by
      rw [exp_neg]
      field_simp
      ring
    have hpos := exp_pos x
    nlinarith
  · have hanti : AntitoneOn (fun x => 2*sqrt x*exp (-x)) (Ici (251/200 : ℝ)) := by
      apply sqrt_derivative_antitone (by norm_num : (0:ℝ)<251/200)
        (ddf := fun x => -exp (-x))
      · intro x hx
        exact ((hasDerivAt_id x).neg.exp).congr_deriv (by simp)
      · intro x hx
        have he := exp_pos (-x)
        nlinarith
    intro x hx
    exact (hanti (show (251/200 : ℝ) ∈ Ici (251/200 : ℝ) by norm_num)
      hx hx).trans first_anchor_derivative_bound
  · exact hz

end HadwigerRamsey4Col
