import ComponentTransfer.ComponentProgram
import HadwigerRamsey4Col.Analytic

open scoped BigOperators
namespace HadwigerRamsey4Col

/-- The optimization program is the existing component program, specialized
at four colours. Its objective is the square root of maximum component entropy. -/
abbrev ComponentInstance := ComponentTransfer.ComponentInstance 4

noncomputable def beta4 : ℝ := ComponentTransfer.beta 4

/-- Coordinates for the four-atom three-pairing pattern, allowing zero masses.
`span` is the fourth colour. For distinct `i,j`, `pair i j` is the off-diagonal
probability in their unique pairing colour, and `diag i j` is that colour's
probability on atom `i`'s diagonal. There is one paired component per unordered
pair, with diagonal probabilities `diag i j` and `diag j i`. -/
structure PairingData where
  mass : Fin 4 → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  mass_sum : ∑ i, mass i = 1
  span : Fin 4 → Fin 4 → ℝ
  span_nonneg : ∀ i j, 0 ≤ span i j
  span_lt_one : ∀ i j, span i j < 1
  span_symm : ∀ i j, span i j = span j i
  pair : Fin 4 → Fin 4 → ℝ
  pair_nonneg : ∀ i j, i ≠ j → 0 ≤ pair i j
  pair_lt_one : ∀ i j, i ≠ j → pair i j < 1
  pair_symm : ∀ i j, pair i j = pair j i
  diag : Fin 4 → Fin 4 → ℝ
  diag_nonneg : ∀ i j, i ≠ j → 0 ≤ diag i j
  diag_lt_one : ∀ i j, i ≠ j → diag i j < 1
  offdiag_sum : ∀ i j, i ≠ j → span i j + pair i j = 1
  diag_sum : ∀ i, span i i + ∑ j ∈ Finset.univ.erase i, diag i j = 1

namespace PairingData

noncomputable def spanEnergy (I : PairingData) : ℝ :=
  ∑ i, ∑ j, I.mass i * I.mass j * cost (I.span i j)

noncomputable def pairEnergy (I : PairingData) (i j : Fin 4) : ℝ :=
  I.mass i^2 * cost (I.diag i j) + I.mass j^2 * cost (I.diag j i) +
    2*I.mass i*I.mass j*cost (I.pair i j)

theorem pairEnergy_symm (I : PairingData) (i j : Fin 4) :
    I.pairEnergy i j = I.pairEnergy j i := by
  unfold pairEnergy
  rw [I.pair_symm i j]
  ring

end PairingData
end HadwigerRamsey4Col
