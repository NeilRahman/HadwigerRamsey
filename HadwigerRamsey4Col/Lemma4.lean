import HadwigerRamsey4Col.Coefficients
import HadwigerRamsey4Col.EntropyQuadratic

namespace HadwigerRamsey4Col

/-- Lemma 4 of `four_colour_analytic.tex`. Here `weight = (1-p)/p`,
`shiftedWeight = 3*weight-1/4`, `entropy = H`, and `entropySlope = H'`
on the positive axis. Both coefficient definitions are the manuscript's. -/
theorem lemma4 :
    ((1/3 : ℝ) < weight ∧ weight < 11/32) ∧
    (3/4 : ℝ) < shiftedWeight ∧
    (5/4 : ℝ) < alphaCoefficient ∧
    (-1 : ℝ) < gammaCoefficient ∧
    ∀ d : ℝ, |d| ≤ (3/20 : ℝ) →
      entropy weight+entropySlope weight*d-2*d^2 ≤ entropy (weight+d) := by
  refine ⟨weight_bounds, ?_, alpha_coefficient_bound, gamma_coefficient_bound, ?_⟩
  · dsimp [shiftedWeight]
    linarith [weight_bounds.1]
  · intro d hd
    exact entropy_quadratic_lower weight_bounds.1.le hd

end HadwigerRamsey4Col
