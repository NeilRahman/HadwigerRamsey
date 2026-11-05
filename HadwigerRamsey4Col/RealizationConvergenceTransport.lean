import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Matching finite probability distributions

The common diagonal mass is the coordinatewise minimum. The remaining mass
is coupled independently. This gives one coupling for all the graph colours,
with disagreement bounded by the sum of the coordinate mass discrepancies.
-/

namespace HadwigerRamsey4Col.Realization

open Finset
open scoped BigOperators

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The mass left after matching the common diagonal of two distributions. -/
noncomputable def unmatchedMass (p q : K → ℝ) : ℝ :=
  ∑ i, (p i - min (p i) (q i))

/-- A maximal-diagonal coupling, including the zero-residual case. -/
noncomputable def finiteTransport (p q : K → ℝ) (i j : K) : ℝ :=
  (if i = j then min (p i) (q i) else 0) +
    (p i - min (p i) (q i)) * (q j - min (p j) (q j)) / unmatchedMass p q

omit [DecidableEq K] in
lemma unmatchedMass_nonneg (p q : K → ℝ) : 0 ≤ unmatchedMass p q :=
  sum_nonneg fun _ _ => sub_nonneg.mpr (min_le_left _ _)

omit [DecidableEq K] in
lemma residual_sum_eq {p q : K → ℝ} (hsum : ∑ i, p i = ∑ i, q i) :
    ∑ i, (q i - min (p i) (q i)) = unmatchedMass p q := by
  simp only [unmatchedMass, sum_sub_distrib]
  rw [hsum]

omit [DecidableEq K] in
lemma left_residual_zero {p q : K → ℝ} (hzero : unmatchedMass p q = 0) (i : K) :
    p i - min (p i) (q i) = 0 := by
  exact (sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (univ : Finset K)) => sub_nonneg.mpr (min_le_left _ _))).mp
      hzero i (mem_univ i)

lemma right_residual_zero {p q : K → ℝ} (hsum : ∑ i, p i = ∑ i, q i)
    (hzero : unmatchedMass p q = 0) (i : K) :
    q i - min (p i) (q i) = 0 := by
  apply (sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (univ : Finset K)) => sub_nonneg.mpr (min_le_right _ _))).mp
      ((residual_sum_eq hsum).trans hzero) i (mem_univ i)

lemma finiteTransport_nonneg (p q : K → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (i j : K) : 0 ≤ finiteTransport p q i j := by
  unfold finiteTransport
  apply add_nonneg
  · split_ifs <;> simp_all
  · exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
        (sub_nonneg.mpr (min_le_right _ _))) (unmatchedMass_nonneg p q)

lemma finiteTransport_row (p q : K → ℝ) (hsum : ∑ i, p i = ∑ i, q i) (i : K) :
    ∑ j, finiteTransport p q i j = p i := by
  simp only [finiteTransport, sum_add_distrib, ← sum_div, ← mul_sum]
  rw [sum_ite_eq, if_pos (mem_univ i), residual_sum_eq hsum]
  by_cases hzero : unmatchedMass p q = 0
  · rw [left_residual_zero hzero, zero_mul, zero_div, add_zero]
    linarith [left_residual_zero hzero i]
  · rw [mul_div_cancel_right₀ _ hzero]
    ring

lemma finiteTransport_column (p q : K → ℝ) (hsum : ∑ i, p i = ∑ i, q i) (j : K) :
    ∑ i, finiteTransport p q i j = q j := by
  simp only [finiteTransport, sum_add_distrib, ← sum_div, ← sum_mul]
  rw [sum_ite_eq', if_pos (mem_univ j)]
  change min (p j) (q j) +
    unmatchedMass p q * (q j - min (p j) (q j)) / unmatchedMass p q = q j
  by_cases hzero : unmatchedMass p q = 0
  · rw [hzero, zero_mul, zero_div, add_zero]
    linarith [right_residual_zero hsum hzero j]
  · rw [mul_div_cancel_left₀ _ hzero]
    ring

lemma finiteTransport_disagreement_row_le (p q : K → ℝ)
    (hsum : ∑ i, p i = ∑ i, q i) (i : K) :
    (∑ j, if i ≠ j then finiteTransport p q i j else 0) ≤ p i - min (p i) (q i) := by
  calc
    (∑ j, if i ≠ j then finiteTransport p q i j else 0) ≤
        ∑ j, (p i - min (p i) (q i)) * (q j - min (p j) (q j)) /
          unmatchedMass p q := by
      apply sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp only [hij, ne_eq, not_true_eq_false, ↓reduceIte]
        exact div_nonneg (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
          (sub_nonneg.mpr (min_le_right _ _))) (unmatchedMass_nonneg p q)
      · simp [finiteTransport, hij]
    _ = p i - min (p i) (q i) := by
      rw [← sum_div, ← mul_sum, residual_sum_eq hsum]
      by_cases hzero : unmatchedMass p q = 0
      · rw [left_residual_zero hzero, zero_mul, zero_div]
      · exact mul_div_cancel_right₀ _ hzero

/-- The disagreement probability of this common transport is at most the
coordinatewise mass discrepancy. No strict positivity assumption is needed. -/
theorem finiteTransport_disagreement_le (p q : K → ℝ)
    (hsum : ∑ i, p i = ∑ i, q i) :
    (∑ i, ∑ j, if i ≠ j then finiteTransport p q i j else 0) ≤
      ∑ i, |p i - q i| := by
  apply sum_le_sum
  intro i _
  apply (finiteTransport_disagreement_row_le p q hsum i).trans
  by_cases hi : p i ≤ q i
  · rw [min_eq_left hi, sub_self]
    exact abs_nonneg _
  · rw [min_eq_right (le_of_not_ge hi)]
    exact le_abs_self _

end HadwigerRamsey4Col.Realization
