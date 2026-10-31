import HadwigerRamsey.FOpt.Envelope

open scoped BigOperators

namespace HadwigerRamsey

/-- The parameter β in the manuscript. -/
noncomputable def beta : ℝ := FOpt.beta

/-- The function in Lemma 3.6, with the same formula also used at x = 1.
At x = 0 its value is zero, as specified in the manuscript. -/
noncomputable def optimizationFunction (x : ℝ) : ℝ := FOpt.function x

@[simp] theorem optimizationFunction_zero : optimizationFunction 0 = 0 := by
  simp [optimizationFunction,FOpt.function]

/-- Lemma 3.6 (`fopt`): the exact finite-sum inequality, including zero weights. -/
theorem fopt (k : ℕ) (α : Fin k → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hs : ∑ i, α i = 1) :
    ∑ i, optimizationFunction (α i) ≤ Real.log 2 - beta^2 := by
  simpa only [optimizationFunction,FOpt.function,beta,FOpt.beta_sq,FOpt.F] using
    (FOpt.sum_le_of_cubic_envelope Finset.univ α (FOpt.value FOpt.c)
      FOpt.a_nonneg (fun _ hx => FOpt.cubic_envelope hx) (by simpa using hα) hs)

end HadwigerRamsey
