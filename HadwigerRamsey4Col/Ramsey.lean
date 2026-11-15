import ComponentTransfer.Asymptotic
import HadwigerRamsey4Col.Theorem1

open Filter Real
open scoped Topology

namespace HadwigerRamsey4Col

/-- The least order forcing a monochromatic `K_k` minor in every four-colouring. -/
noncomputable abbrev hadwigerRamsey (k : ℕ) : ℕ :=
  ComponentTransfer.hadwigerRamsey 4 k

/-- The exact constant in Proposition 4.2, for any root satisfying its specification. -/
theorem beta4_eq_of_root {p : ℝ} (hp : 0 < p ∧ p < 1 ∧ 3*p^6+2*p-2=0) :
    beta4 = sqrt (-(3/4 : ℝ)*log p) := by
  have he : p = parameter := ExistsUnique.unique exists_unique_parameter hp parameter_spec
  subst p
  exact beta4_eq

/-- Proposition 4.2: the four-colour Hadwiger--Ramsey asymptotic, using Proposition 4.1.
The leading constant is evaluated by `beta4_eq_of_root`; the declaration name is retained. -/
theorem theorem1_1 :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds beta4⁻¹) := by
  simpa only [hadwigerRamsey, beta4] using ComponentTransfer.theorem5 4 (by decide)

/-- Proposition 4.2 with the exact algebraic-logarithmic constant substituted. -/
theorem theorem1_1_explicit {p : ℝ} (hp : 0 < p ∧ p < 1 ∧ 3*p^6+2*p-2=0) :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds (Real.sqrt (-(3/4 : ℝ)*Real.log p))⁻¹) := by
  rw [← beta4_eq_of_root hp]
  exact theorem1_1

end HadwigerRamsey4Col
