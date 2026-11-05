import HadwigerRamsey4Col.CapacityCalculus
import HadwigerRamsey4Col.CapacityNumerics

open Real Set
namespace HadwigerRamsey4Col

noncomputable def capacityLog (z : ℝ) : ℝ := log ((3-exp (-z))/2)
noncomputable def capacityLogTest (z : ℝ) : ℝ := 2*z/(3*exp z-1)-capacityLog z
noncomputable def capacityLogTestSlope (z : ℝ) : ℝ :=
  (3*exp z*(1-2*z)-1)/(3*exp z-1)^2

lemma capacity_den_pos {z : ℝ} (hz : 0 ≤ z) : 0 < 3*exp z-1 := by
  have he : 1 ≤ exp z := one_le_exp hz
  linarith

lemma capacity_arg_pos {z : ℝ} (hz : 0 ≤ z) : 0 < (3-exp (-z))/2 := by
  have he : exp (-z) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  linarith

lemma capacityLog_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt capacityLog (1/(3*exp z-1)) z := by
  have he := (hasDerivAt_id z).neg.exp
  have h := (((hasDerivAt_const z 3).sub he).div_const 2).log
    (ne_of_gt (capacity_arg_pos hz))
  apply h.congr_deriv
  change (0-exp (-z)*(-1))/2/((3-exp (-z))/2) = 1/(3*exp z-1)
  rw [exp_neg]
  field_simp [ne_of_gt (capacity_den_pos hz)]
  ring

lemma capacityLog_derivative_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun x => 1/(3*exp x-1))
      (-3*exp z/(3*exp z-1)^2) z := by
  have h := (hasDerivAt_const z 1).div
    (((hasDerivAt_exp z).const_mul 3).sub_const 1) (ne_of_gt (capacity_den_pos hz))
  apply h.congr_deriv
  ring

lemma capacityLogTest_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt capacityLogTest (capacityLogTestSlope z) z := by
  have h := (((hasDerivAt_id z).const_mul 2).div
    (((hasDerivAt_exp z).const_mul 3).sub_const 1) (ne_of_gt (capacity_den_pos hz))).sub
    (capacityLog_hasDerivAt hz)
  apply h.congr_deriv
  dsimp [capacityLogTestSlope]
  field_simp [ne_of_gt (capacity_den_pos hz)]
  ring

lemma capacityLogTestSlope_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt capacityLogTestSlope
      (-3*exp z*(3*exp z*(3-2*z)-(3+2*z))/(3*exp z-1)^3) z := by
  have hN := ((((hasDerivAt_exp z).const_mul 3).mul
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul 2))).sub_const 1)
  have hD := ((((hasDerivAt_exp z).const_mul 3).sub_const 1).pow 2)
  have h := hN.div hD (pow_ne_zero 2 (ne_of_gt (capacity_den_pos hz)))
  apply h.congr_deriv
  dsimp
  field_simp [ne_of_gt (capacity_den_pos hz)]
  ring

lemma capacityLogTest_concave :
    ConcaveOn ℝ (Icc 0 (41/40 : ℝ)) capacityLogTest := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := capacityLogTestSlope)
    (f'' := fun z => -3*exp z*(3*exp z*(3-2*z)-(3+2*z))/(3*exp z-1)^3)
  · intro z hz
    exact (capacityLogTest_hasDerivAt hz.1).continuousAt.continuousWithinAt
  · intro z hz
    exact (capacityLogTest_hasDerivAt (interior_subset hz).1).hasDerivWithinAt
  · intro z hz
    exact (capacityLogTestSlope_hasDerivAt (interior_subset hz).1).hasDerivWithinAt
  · intro z hz
    have hz' := interior_subset hz
    have he := add_one_le_exp z
    have hpos : 0 ≤ 3-2*z := by linarith [hz'.2]
    have hm := mul_le_mul_of_nonneg_right he hpos
    have hquad := mul_nonneg hz'.1 (sub_nonneg.mpr hz'.2)
    have hnum : 0 ≤ 3*exp z*(3-2*z)-(3+2*z) := by nlinarith [hz'.1,hz'.2]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by have := exp_pos z; linarith) hnum
    · exact (pow_pos (capacity_den_pos hz'.1) 3).le

end HadwigerRamsey4Col
