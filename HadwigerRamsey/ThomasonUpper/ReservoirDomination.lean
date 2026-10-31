import HadwigerRamsey.ThomasonUpper.Domination
import HadwigerRamsey.ThomasonUpper.Selection

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

/-- The entire allocation of the sets M_a from the appendix, with the
reservoir size and neighbor-count hypotheses stated explicitly. -/
theorem reservoir_dominating_sets {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (G : SimpleGraph V)
    (W : I → Finset V) (D : Finset V) (K : ℕ)
    (hW : ∀ i, (W i).Nonempty) (hWK : ∀ i, (W i).card ≤ K)
    (ε R : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hR : 0 < R)
    (hD : (D.card : ℝ) ≤ 2*R)
    (hdeg : ∀ i v, v ∈ W i → ε*R/2 ≤ (D.filter (G.Adj v)).card)
    (hbudget : (Fintype.card I : ℝ) * (⌈log (K : ℝ) / (-log (1-ε/8))⌉₊ + 1) ≤ ε*R/4) :
    ∃ M : I → Finset V,
      (∀ i, M i ⊆ D ∧
        (M i).card ≤ ⌈log (K : ℝ) / (-log (1-ε/8))⌉₊ + 1 ∧
        ∀ v ∈ W i, ∃ u ∈ M i, G.Adj v u) ∧
      ∀ i j, i ≠ j → Disjoint (M i) (M j) := by
  classical
  let L := ⌈log (K : ℝ) / (-log (1-ε/8))⌉₊ + 1
  apply disjoint_reservoir_selection D L (fun i M => ∀ v ∈ W i, ∃ u ∈ M, G.Adj v u)
  intro i U _hUD hU
  have hUR : (U.card : ℝ) ≤ ε*R/4 := by
    have huR : (U.card : ℝ) ≤ (Fintype.card I : ℝ) * L := by exact_mod_cast hU
    exact huR.trans (by simpa [L] using hbudget)
  have hremain : ∀ v ∈ W i, ε*R/4 ≤ ((D \ U).filter (G.Adj v)).card := by
    intro v hv
    have hcard := card_le_card_sdiff_add_card (s := D.filter (G.Adj v)) (t := U)
    have heq : (D.filter (G.Adj v)) \ U = (D \ U).filter (G.Adj v) := by
      ext x; simp only [mem_sdiff, mem_filter]; tauto
    rw [heq] at hcard
    have hc : ((D.filter (G.Adj v)).card : ℝ) ≤
        ((D \ U).filter (G.Adj v)).card + (U.card : ℝ) := by exact_mod_cast hcard
    linarith [hdeg i v hv]
  have hB : (D \ U).Nonempty := by
    obtain ⟨v, hv⟩ := hW i
    have hpos : (0 : ℝ) < ((D \ U).filter (G.Adj v)).card :=
      (by positivity : (0 : ℝ) < ε*R/4).trans_le (hremain v hv)
    have hposN : 0 < ((D \ U).filter (G.Adj v)).card := by exact_mod_cast hpos
    exact (card_pos.mp hposN).mono (filter_subset _ _)
  have hθ : 0 < ε/8 := by positivity
  have hθ1 : ε/8 < 1 := by linarith
  have hdeg' : ∀ v ∈ W i,
      (ε/8) * ((D \ U).card : ℝ) ≤ ((D \ U).filter (G.Adj v)).card := by
    intro v hv
    have hcard : ((D \ U).card : ℝ) ≤ D.card := by
      exact_mod_cast card_le_card (sdiff_subset : D \ U ⊆ D)
    have hD' : ((D \ U).card : ℝ) ≤ 2*R := hcard.trans hD
    have hm := mul_le_mul_of_nonneg_left hD' hθ.le
    nlinarith [hremain v hv]
  obtain ⟨M, hM, hML, hdom⟩ := exists_dominating_set (W i) (D \ U) (hW i) hB
    G.Adj (ε/8) hθ hθ1 hdeg'
  refine ⟨M, hM, hML.trans ?_, hdom⟩
  apply Nat.add_le_add_right
  apply Nat.ceil_le_ceil
  apply div_le_div_of_nonneg_right
  · apply log_le_log
    · exact_mod_cast (hW i).card_pos
    · exact_mod_cast hWK i
  · have := log_neg (by linarith : 0 < 1-ε/8) (by linarith : 1-ε/8 < 1)
    linarith

end HadwigerRamsey.ThomasonUpper
