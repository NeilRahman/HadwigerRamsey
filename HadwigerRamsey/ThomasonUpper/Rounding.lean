import Mathlib

open scoped BigOperators
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Round nonnegative weights to natural numbers with their exact prescribed
total. Each coordinate changes by at most one. This is the finite rounding
step in appendix A.3. -/
theorem rounded_counts {I : Type*} [Fintype I] (α : I → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) (ℓ : ℕ) :
    ∃ m : I → ℕ, (∑ i, m i) = ℓ ∧
      (∀ i, |(m i : ℝ) - α i * ℓ| ≤ 1) ∧
      (∀ i, ⌊α i * ℓ⌋₊ ≤ m i) := by
  classical
  let b := fun i => ⌊α i * ℓ⌋₊
  have hscaled : ∑ i, α i * ℓ = (ℓ : ℝ) := by rw [← sum_mul, hsum, one_mul]
  have hfloor : ∀ i, (b i : ℝ) ≤ α i * ℓ := fun i =>
    Nat.floor_le (mul_nonneg (hα i) (Nat.cast_nonneg ℓ))
  have hnext : ∀ i, α i * ℓ ≤ (b i : ℝ) + 1 := fun i => (Nat.lt_floor_add_one _).le
  have hb : ∑ i, b i ≤ ℓ := by
    have hh := sum_le_sum fun i (_ : i ∈ (univ : Finset I)) => hfloor i
    rw [hscaled] at hh
    exact_mod_cast hh
  have hr : ℓ - ∑ i, b i ≤ Fintype.card I := by
    have hh := sum_le_sum fun i (_ : i ∈ (univ : Finset I)) => hnext i
    rw [hscaled, sum_add_distrib] at hh
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, ← Nat.cast_sum] at hh
    have hc : ℓ ≤ (∑ i, b i) + Fintype.card I := by exact_mod_cast hh
    omega
  obtain ⟨T, _, hT⟩ := exists_subset_card_eq (s := (univ : Finset I))
    (n := ℓ - ∑ i, b i) (by simpa only [card_univ] using hr)
  let m := fun i => b i + if i ∈ T then 1 else 0
  refine ⟨m, ?_, ?_, ?_⟩
  · have hm : ∑ i, m i = (∑ i, b i) + T.card := by
      simp [m, sum_add_distrib]
    rw [hm, hT]
    omega
  · intro i
    dsimp [m]
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith [hfloor i, hnext i]
  · intro i
    dsimp [m, b]
    omega

/-- The manuscript's normalized rounding bound, with positivity once every
unrounded coordinate is at least one. -/
theorem positive_rounded_masses {I : Type*} [Fintype I] (α : I → ℝ)
    (hsum : ∑ i, α i = 1) {a : ℝ} (ha : 0 < a) (hα : ∀ i, a ≤ α i)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hlarge : 1 ≤ a*ℓ) :
    ∃ m : I → ℕ, (∑ i, m i) = ℓ ∧ (∀ i, 0 < m i) ∧
      (∀ i, |(m i : ℝ)/(ℓ : ℝ) - α i| ≤ 1/(ℓ : ℝ)) := by
  obtain ⟨m, hm, herr, hfloor⟩ := rounded_counts α (fun i => ha.le.trans (hα i)) hsum ℓ
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  refine ⟨m, hm, ?_, ?_⟩
  · intro i
    have hprod : 1 ≤ α i*ℓ := hlarge.trans (mul_le_mul_of_nonneg_right (hα i) hℓR.le)
    exact (Nat.floor_pos.mpr hprod).trans_le (hfloor i)
  · intro i
    have he : (m i : ℝ)/(ℓ : ℝ)-α i = ((m i : ℝ)-α i*ℓ)/(ℓ : ℝ) := by field_simp
    rw [he, abs_div, abs_of_pos hℓR]
    exact div_le_div_of_nonneg_right (herr i) hℓR.le

end HadwigerRamsey.ThomasonUpper
