import ComponentTransfer.Asymptotic
import HadwigerRamsey4Col.Theorem1

open Filter Real
open scoped Topology

namespace HadwigerRamsey4Col

/-- The least order forcing a monochromatic `K_k` minor in every four-colouring. -/
noncomputable abbrev hadwigerRamsey (k : ℕ) : ℕ :=
  ComponentTransfer.hadwigerRamsey 4 k

/-- The exact four-colour constant, for any root satisfying the manuscript's specification. -/
theorem beta4_eq_of_root {p : ℝ} (hp : 0 < p ∧ p < 1 ∧ 3*p^6+2*p-2=0) :
    beta4 = sqrt (-(3/4 : ℝ)*log p) := by
  have he : p = parameter := ExistsUnique.unique exists_unique_parameter hp parameter_spec
  subst p
  exact beta4_eq

/-- The four-colour analogue of Theorem 1.1: the Hadwiger--Ramsey asymptotic.
The leading constant is evaluated by `beta4_eq_of_root`. -/
theorem theorem1_1 :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds beta4⁻¹) := by
  simpa only [hadwigerRamsey, beta4] using ComponentTransfer.theorem5 4 (by decide)

/-- The same asymptotic with the exact algebraic-logarithmic constant substituted. -/
theorem theorem1_1_explicit {p : ℝ} (hp : 0 < p ∧ p < 1 ∧ 3*p^6+2*p-2=0) :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds (Real.sqrt (-(3/4 : ℝ)*Real.log p))⁻¹) := by
  rw [← beta4_eq_of_root hp]
  exact theorem1_1

end HadwigerRamsey4Col
