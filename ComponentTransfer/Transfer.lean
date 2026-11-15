import ComponentTransfer.TransferConclusion
import ComponentTransfer.TransferFinitePresentation
import ComponentTransfer.TransferComponentLabels

open scoped Classical Topology
open Filter Real
open HadwigerRamsey

namespace ComponentTransfer

/-- The lower bound supporting Proposition 4.1. Common coloured compactness,
connected-component decomposition, entropy lifting, and finite truncation
supply the two graphon structure inputs to the final contradiction. -/
theorem transferBound (r : ℕ) (hr : 2 ≤ r) : TransferBound r (beta r) := by
  apply Transfer.transferBound_of_graphon_results hr
  · intro N hNpos hN G hG
    obtain ⟨W,s,hs,hsum,hconv⟩ := Transfer.finite_coloured_compactness_pos N hNpos hN G hG
    exact ⟨s,hs,W,hsum,hconv⟩
  · exact Transfer.exists_colored_components

/-- **Theorem 3 of `comptransfer.tex`, supporting Proposition 4.1.** Every sufficiently large complete
`r`-edge-colouring has a colour with the asserted Hadwiger-number lower bound. -/
theorem theorem3 (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Fin r → SimpleGraph (Fin n),
      IsDecomposition G → ∃ c : Fin r,
        (beta r-ε)*(n : ℝ)/sqrt (log (n : ℝ)) ≤ hadwigerNumber (G c) :=
  eventually_atTop.mp (transferBound r hr ε hε)

end ComponentTransfer
