import HadwigerRamsey.ThomasonUpper.FiniteExpectations

open scoped BigOperators Classical ENNReal
open Finset

namespace HadwigerRamsey.ThomasonUpper

theorem uniform_probability_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A B : Set Ω} (h : A ⊆ B) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure A).toReal ≤
      ((PMF.uniformOfFintype Ω).toOuterMeasure B).toReal := by
  rw [uniform_probability_eq_expect,uniform_probability_eq_expect]
  apply expect_le_expect
  intro p hp
  by_cases ha : p ∈ A
  · simp [ha,h ha]
  · simp only [if_neg ha]
    split_ifs <;> norm_num

/-- Decompose a finite uniform event according to a finite-valued random
variable. This is the total-probability identity used instead of conditioning. -/
theorem uniform_probability_sum_fibers {Ω X : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype X] (f : Ω → X) (A : Set Ω) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure A).toReal =
      ∑ x, ((PMF.uniformOfFintype Ω).toOuterMeasure {p | f p = x ∧ p ∈ A}).toReal := by
  classical
  simp_rw [uniform_probability_eq_expect]
  have hh : ∀ p, (if p ∈ A then (1 : ℝ) else 0) =
      ∑ x, if f p = x ∧ p ∈ A then (1 : ℝ) else 0 := by
    intro p
    rw [sum_eq_single (f p)]
    · simp
    · intro x hx hne
      simp [hne.symm]
    · simp
  simp only [Set.mem_ofPred_eq]
  simp_rw [hh]
  rw [← expect_sum_comm]
  apply expect_congr rfl
  intro p hp
  apply sum_congr rfl
  intro x hx
  by_cases h : f p = x ∧ p ∈ A <;> simp [h]

end HadwigerRamsey.ThomasonUpper
