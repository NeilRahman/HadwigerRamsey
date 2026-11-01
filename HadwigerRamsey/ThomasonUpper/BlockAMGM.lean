import HadwigerRamsey.ThomasonUpper.NonneighborWeights

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- AM-GM with a prescribed positive upper bound on the arithmetic mean.
The zero-factor case is separated before using the existing log estimate. -/
theorem product_le_pow_of_sum_le {I : Type*} (S : Finset I) (z : I → ℝ)
    {q : ℝ} (hq : 0 < q) (hz : ∀ i ∈ S, 0 ≤ z i)
    (hmean : (∑ i ∈ S, z i) ≤ S.card*q) :
    (∏ i ∈ S, z i) ≤ q^S.card := by
  classical
  by_cases hzero : ∃ i ∈ S, z i = 0
  · obtain ⟨i,hi,hzi⟩ := hzero
    rw [prod_eq_zero hi hzi]
    positivity
  · have hp : ∀ i ∈ S, 0 < z i := by
      intro i hi
      exact lt_of_le_of_ne (hz i hi) (Ne.symm (fun hh => hzero ⟨i,hi,hh⟩))
    apply (log_le_log_iff (prod_pos hp) (pow_pos hq _)).mp
    rw [log_prod (fun i hi => (hp i hi).ne'),log_pow]
    exact sum_log_le_card_mul_log S z hp hq hmean

/-- The classwise block proportions have product at most rho to the
ell-th power. This is the AM-GM step in the random-part estimate of A.1. -/
theorem multitype_block_product_le_weight {k L : ℕ} (ell : Fin k → ℕ)
    (hL : 0 < L) (d : Fin k → ℝ)
    (z : ∀ j, Fin (ell j) → ℝ) (hd : ∀ j, 0 < d j)
    (hz : ∀ j a, 0 ≤ z j a)
    (hmean : ∀ j, (∑ a, z j a) ≤ (ell j : ℝ)*d j) :
    (∏ j, ∏ a, z j a) ≤ (∏ j, (d j)^((ell j : ℝ)/L))^L := by
  have he : (∏ j, (d j)^((ell j : ℝ)/L))^L = ∏ j, (d j)^(ell j) := by
    rw [← prod_pow]
    apply prod_congr rfl
    intro j hj
    rw [← rpow_natCast,← rpow_mul (hd j).le]
    have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [div_mul_cancel₀ _ hLR,rpow_natCast]
  rw [he]
  apply prod_le_prod
  · intro j hj
    exact prod_nonneg (fun a _ => hz j a)
  · intro j hj
    simpa using product_le_pow_of_sum_le univ (z j) (hd j) (fun a _ => hz j a)
      (by simpa using hmean j)

end HadwigerRamsey.ThomasonUpper
