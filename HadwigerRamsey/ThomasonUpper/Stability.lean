import Mathlib

open scoped BigOperators
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- A uniform logarithm estimate on a positive half-line. This is the
analytic estimate used after the density perturbations in `lem:stability`. -/
theorem log_lipschitz {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |log x - log y| ≤ |x-y| / a := by
  have hxp := ha.trans_le hx
  have hyp := ha.trans_le hy
  have hdir : ∀ u v : ℝ, a ≤ u → a ≤ v → v ≤ u →
      log u - log v ≤ (u-v)/a := by
    intro u v hu hv hvu
    have hup := ha.trans_le hu
    have hvp := ha.trans_le hv
    have hlog : 0 ≤ log u - log v := sub_nonneg.mpr (log_le_log hvp hvu)
    have hl := Real.log_le_sub_one_of_pos (div_pos hup hvp)
    rw [log_div hup.ne' hvp.ne'] at hl
    have hl' : v * (log u-log v) ≤ u-v := by
      have h' : log u-log v ≤ (u-v)/v := by
        calc
          _ ≤ u/v-1 := hl
          _ = (u-v)/v := by field_simp
      have := (le_div_iff₀ hvp).mp h'
      nlinarith
    apply (le_div_iff₀ ha).mpr
    have := mul_le_mul_of_nonneg_right hv hlog
    nlinarith
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (log_le_log hyp hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hdir x y hx hy hyx
  · rw [abs_sub_comm (log x), abs_sub_comm x]
    rw [abs_of_nonneg (sub_nonneg.mpr (log_le_log hxp hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hdir y x hy hx hxy

/-- Changing two probability vectors changes their product weights by at
most twice their total absolute change. -/
theorem product_mass_stability {I : Type*} [Fintype I]
    (α β : I → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ i, β i = 1) :
    (∑ i, ∑ j, |α i * α j - β i * β j|) ≤ 2 * ∑ i, |α i-β i| := by
  calc
    _ ≤ ∑ i, ∑ j, (|α i-β i| * α j + β i * |α j-β j|) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      calc
        _ = |(α i-β i)*α j + β i*(α j-β j)| := by congr 1; ring
        _ ≤ |(α i-β i)*α j| + |β i*(α j-β j)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hα j), abs_of_nonneg (hβ i)]
    _ = _ := by
      simp_rw [sum_add_distrib, ← mul_sum, ← sum_mul, hαsum, hβsum, mul_one, one_mul]
      ring

/-- Stability of the entropy sum under uniformly small changes to the
complementary densities and small total changes to the class masses. -/
theorem lambda_stability {I : Type*} [Fintype I]
    (α β : I → ℝ) (q r : I → I → ℝ) {a d : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ i, β i = 1)
    (hq : ∀ i j, a ≤ q i j ∧ q i j ≤ 1)
    (hr : ∀ i j, a ≤ r i j ∧ r i j ≤ 1)
    (hd : ∀ i j, |q i j-r i j| ≤ d) :
    |(∑ i, ∑ j, α i*α j*(-log (q i j))) -
      ∑ i, ∑ j, β i*β j*(-log (r i j))| ≤
      d/a + 2*log (1/a)*(∑ i, |α i-β i|) := by
  have hlogbound : ∀ i j, |log (r i j)| ≤ log (1/a) := by
    intro i j
    have hpos := ha.trans_le (hr i j).1
    rw [abs_of_nonpos (log_nonpos hpos.le (hr i j).2), one_div, log_inv]
    exact neg_le_neg (log_le_log ha (hr i j).1)
  have hlogB : 0 ≤ log (1/a) := by
    rw [one_div, log_inv]
    exact neg_nonneg.mpr (log_nonpos ha.le ha1)
  have hterms : ∀ i j,
      |α i*α j*(-log (q i j)) - β i*β j*(-log (r i j))| ≤
        α i*α j*(d/a) + |α i*α j-β i*β j| * log (1/a) := by
    intro i j
    calc
      _ = |(α i*α j) * (log (r i j)-log (q i j)) +
          (α i*α j-β i*β j)*(-log (r i j))| := by congr 1; ring
      _ ≤ |α i*α j| * |log (r i j)-log (q i j)| +
          |α i*α j-β i*β j| * |log (r i j)| := by
        simpa only [abs_mul, abs_neg] using abs_add_le
          ((α i*α j) * (log (r i j)-log (q i j)))
          ((α i*α j-β i*β j)*(-log (r i j)))
      _ ≤ α i*α j*(d/a) + |α i*α j-β i*β j| * log (1/a) := by
        rw [abs_of_nonneg (mul_nonneg (hα i) (hα j))]
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hα i) (hα j))
          exact (log_lipschitz ha (hr i j).1 (hq i j).1).trans
            (div_le_div_of_nonneg_right (by simpa [abs_sub_comm] using hd i j) ha.le)
        · exact mul_le_mul_of_nonneg_left (hlogbound i j) (abs_nonneg _)
  calc
    _ = |∑ i, ∑ j, (α i*α j*(-log (q i j))-β i*β j*(-log (r i j)))| := by
      simp only [sum_sub_distrib]
    _ ≤ ∑ i, ∑ j, |α i*α j*(-log (q i j))-β i*β j*(-log (r i j))| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (α i*α j*(d/a) + |α i*α j-β i*β j| * log (1/a)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hterms i j
    _ = d/a + (∑ i, ∑ j, |α i*α j-β i*β j|)*log (1/a) := by
      simp_rw [sum_add_distrib, mul_assoc, ← mul_sum, ← sum_mul, hαsum, one_mul]
    _ ≤ _ := add_le_add_left (by
      nlinarith [mul_le_mul_of_nonneg_right
        (product_mass_stability α β hα hβ hαsum hβsum) hlogB]) _

end HadwigerRamsey.ThomasonUpper
