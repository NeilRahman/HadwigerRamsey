import ComponentTransfer.ComponentProgram
import ComponentTransfer.Ramsey
import ComponentTransfer.Transfer
import ComponentTransfer.Construction

open Filter Real
open scoped Topology

namespace ComponentTransfer

/-- The conclusion of Proposition 4.1, conditional on the two graph bounds.
This reusable deduction is instantiated unconditionally by `theorem5` below. -/
theorem theorem5_of_theorems3_and4 (r : ℕ) (hr : 2 ≤ r)
    (h3 : TransferBound r (beta r)) (h4 : ConstructionBound r (beta r)) :
    Tendsto (fun k : ℕ => (hadwigerRamsey r k : ℝ) /
      ((k : ℝ) * sqrt (log (k : ℝ)))) atTop (𝓝 (beta r)⁻¹) :=
  ramsey_asymptotic_of_bounds (beta_pos hr) h3 h4

/-- **Proposition 4.1 (Theorem 5 of `comptransfer.tex`).** For every fixed `r ≥ 2`, the
Hadwiger--Ramsey number divided by `k * sqrt(log k)` tends to `beta r` inverse.
Both graph bounds are supplied by Theorems 3 and 4 of that companion source. -/
theorem theorem5 (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (hadwigerRamsey r k : ℝ) /
      ((k : ℝ) * sqrt (log (k : ℝ)))) atTop (𝓝 (beta r)⁻¹) :=
  theorem5_of_theorems3_and4 r hr (transferBound r hr) (constructionBound r hr)

end ComponentTransfer
