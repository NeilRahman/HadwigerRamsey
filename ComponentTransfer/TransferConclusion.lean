import ComponentTransfer.TransferSequence
import ComponentTransfer.TransferGraphon

open scoped Classical Topology BigOperators unitInterval
open MeasureTheory Filter Real
open HadwigerRamsey
open ComponentTransfer.Realization

namespace ComponentTransfer.Transfer

/-- The final contradiction in the transfer theorem, with the two graphon
structure results isolated as reusable inputs. -/
theorem transferBound_of_graphon_results {r : ℕ} (hr : 2 ≤ r)
    (hcompact : ∀ (N : ℕ → ℕ), (∀ n, 0 < N n) → Tendsto N atTop atTop →
      ∀ (G : ∀ n, Fin r → SimpleGraph (Fin (N n))), (∀ n, IsDecomposition (G n)) →
      ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ W : Fin r → GraphonI,
        (∀ᵐ p ∂(volume : Measure I).prod volume, ∑ c, (W c).toAEEqFun p = 1) ∧
        FiniteGraphCommonCutConverges (volume : Measure I) (N ∘ s) (fun n => G (s n)) W)
    (hcomponents : ∀ W : Fin r → GraphonI, Nonempty (ColoredComponents W)) :
    TransferBound r (beta r) := by
  by_contra hnot
  obtain ⟨B,hB,hBbeta,N,hN,hN2,G,hG,hupper⟩ :=
    exists_bad_sequence (by omega : 0 < r) (beta_pos hr) hnot
  obtain ⟨s,hs,W,hsum,hconv⟩ := hcompact N (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hN2 n)) hN G hG
  obtain ⟨D⟩ := hcomponents W
  have hbound := D.beta_le_of_bounded_sequence hr hsum (N ∘ s)
    (hN.comp hs.tendsto_atTop) (fun n => G (s n)) hconv hB (fun n c => hupper (s n) c)
  linarith

end ComponentTransfer.Transfer
