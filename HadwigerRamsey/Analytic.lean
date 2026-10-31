import Mathlib

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey

/-- The analytic core of the permissible-partition estimate (finite Jensen). -/
theorem sum_exp_neg_ge {ι : Type*} (t : Finset ι) (W : ι → ℝ)
    (ht : t.Nonempty) :
    (t.card : ℝ) * exp (-(∑ i ∈ t, W i) / t.card) ≤ ∑ i ∈ t, exp (-W i) := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have h := convexOn_exp.map_sum_le
    (t := t) (w := fun _ => (t.card : ℝ)⁻¹) (p := fun i => -W i)
    (fun _ _ => inv_nonneg.mpr hc.le) (by simp [ne_of_gt hc])
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum, Finset.sum_neg_distrib] at h
  calc
    (t.card : ℝ) * exp (-(∑ i ∈ t, W i) / t.card)
        = t.card * exp ((t.card : ℝ)⁻¹ * -(∑ i ∈ t, W i)) := by congr 2; ring
    _ ≤ t.card * ((t.card : ℝ)⁻¹ * ∑ i ∈ t, exp (-W i)) := mul_le_mul_of_nonneg_left h hc.le
    _ = ∑ i ∈ t, exp (-W i) := by field_simp

/-- Product bound used for one fixed partition; no asymptotic assumptions. -/
theorem permissible_product_bound {ι : Type*} (t : Finset ι) (W : ι → ℝ)
    (ht : t.Nonempty) (hW : ∀ i ∈ t, 0 ≤ W i) {T : ℝ}
    (hT : ∑ i ∈ t, W i ≤ T) :
    ∏ i ∈ t, (1 - exp (-W i)) ≤
      exp (-(t.card : ℝ) * exp (-T / t.card)) := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hprod : ∏ i ∈ t, (1 - exp (-W i)) ≤ ∏ i ∈ t, exp (-exp (-W i)) := by
    apply Finset.prod_le_prod
    · intro i hi
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hW i hi))
      linarith
    · intro i hi
      have := Real.add_one_le_exp (-exp (-W i))
      linarith
  have hsum : t.card * exp (-T / t.card) ≤ ∑ i ∈ t, exp (-W i) := by
    calc
      t.card * exp (-T / t.card) ≤ t.card * exp (-(∑ i ∈ t, W i) / t.card) := by
        gcongr
      _ ≤ _ := sum_exp_neg_ge t W ht
  calc
    _ ≤ ∏ i ∈ t, exp (-exp (-W i)) := hprod
    _ = exp (-(∑ i ∈ t, exp (-W i))) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end HadwigerRamsey
