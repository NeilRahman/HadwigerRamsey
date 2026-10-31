import HadwigerRamsey.ThomasonUpper.Stability

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The regularized logarithmic weight used in appendix A.3. -/
noncomputable def regularizedLog (τ x : ℝ) : ℝ := -log (min 1 (x+τ))

theorem regularizedLog_error {a τ x : ℝ} (ha : 0 < a)
    (hτ : 0 ≤ τ) (hx : a ≤ x) (hx1 : x ≤ 1) :
    0 ≤ -log x - regularizedLog τ x ∧
      -log x - regularizedLog τ x ≤ τ/a := by
  have hxpos := ha.trans_le hx
  have hmin : x ≤ min 1 (x+τ) := le_min hx1 (by linarith)
  have hd : |min 1 (x+τ)-x| ≤ τ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmin)]
    linarith [min_le_right (1:ℝ) (x+τ)]
  have hlog := log_le_log hxpos hmin
  have hl := (log_lipschitz ha (hx.trans hmin) hx).trans
    (div_le_div_of_nonneg_right hd ha.le)
  unfold regularizedLog
  rw [abs_of_nonneg (sub_nonneg.mpr hlog)] at hl
  constructor <;> linarith

theorem regularizedLog_lipschitz {a τ x y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hτ : 0 ≤ τ) (hx : a ≤ x) (hy : a ≤ y) :
    |regularizedLog τ x - regularizedLog τ y| ≤ |x-y|/a := by
  have hminx : a ≤ min 1 (x+τ) := le_min ha1 (by linarith)
  have hminy : a ≤ min 1 (y+τ) := le_min ha1 (by linarith)
  have hm : |min 1 (x+τ)-min 1 (y+τ)| ≤ |x-y| := by
    simpa only [sub_self, abs_zero, add_sub_add_right_eq_sub, max_eq_right (abs_nonneg (x-y))]
      using abs_min_sub_min_le_max (1:ℝ) (x+τ) 1 (y+τ)
  unfold regularizedLog
  rw [neg_sub_neg, abs_sub_comm]
  exact (log_lipschitz ha hminx hminy).trans
    (div_le_div_of_nonneg_right hm ha.le)

noncomputable def regularizedLambda {I : Type*} [Fintype I]
    (α : I → ℝ) (q : I → I → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, ∑ j, α i*α j*regularizedLog τ (q i j)

/-- Regularization loses at most τ/a from the original entropy sum,
with the exact probability-vector normalization used in A.3. -/
theorem regularizedLambda_error {I : Type*} [Fintype I]
    (α : I → ℝ) (q : I → I → ℝ) {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 ≤ τ) (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = 1) (hq : ∀ i j, a ≤ q i j ∧ q i j ≤ 1) :
    0 ≤ (∑ i, ∑ j, α i*α j*(-log (q i j))) - regularizedLambda α q τ ∧
      (∑ i, ∑ j, α i*α j*(-log (q i j))) - regularizedLambda α q τ ≤ τ/a := by
  have he : (∑ i, ∑ j, α i*α j*(-log (q i j))) - regularizedLambda α q τ =
      ∑ i, ∑ j, α i*α j*(-log (q i j)-regularizedLog τ (q i j)) := by
    simp only [regularizedLambda, mul_sub, sum_sub_distrib]
  rw [he]
  constructor
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hα i) (hα j))
        (regularizedLog_error ha hτ (hq i j).1 (hq i j).2).1
  · calc
      _ ≤ ∑ i, ∑ j, α i*α j*(τ/a) := sum_le_sum fun i _ => sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left
          (regularizedLog_error ha hτ (hq i j).1 (hq i j).2).2
          (mul_nonneg (hα i) (hα j))
      _ = τ/a := by simp_rw [mul_assoc, ← mul_sum, ← sum_mul, hsum, one_mul]

/-- Uniform stability for the regularized sum. The truncation at one is
nonexpansive, so the existing logarithmic-sum stability theorem applies. -/
theorem regularizedLambda_stability {I : Type*} [Fintype I]
    (α β : I → ℝ) (q r : I → I → ℝ) {a τ d : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 ≤ τ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hsumα : ∑ i, α i = 1) (hsumβ : ∑ i, β i = 1)
    (hq : ∀ i j, a ≤ q i j) (hr : ∀ i j, a ≤ r i j)
    (hd : ∀ i j, |q i j-r i j| ≤ d) :
    |regularizedLambda α q τ - regularizedLambda β r τ| ≤
      d/a + 2*log (1/a)*(∑ i, |α i-β i|) := by
  apply lambda_stability α β
    (fun i j => min 1 (q i j+τ)) (fun i j => min 1 (r i j+τ)) ha ha1 hα hβ hsumα hsumβ
  · intro i j
    exact ⟨le_min ha1 (by linarith [hq i j]), min_le_left _ _⟩
  · intro i j
    exact ⟨le_min ha1 (by linarith [hr i j]), min_le_left _ _⟩
  · intro i j
    have hm := abs_min_sub_min_le_max (1:ℝ) (q i j+τ) 1 (r i j+τ)
    have hh : |min 1 (q i j+τ)-min 1 (r i j+τ)| ≤ |q i j-r i j| := by
      simpa only [sub_self, abs_zero, add_sub_add_right_eq_sub,
        max_eq_right (abs_nonneg (q i j-r i j))] using hm
    exact hh.trans (hd i j)

end HadwigerRamsey.ThomasonUpper
