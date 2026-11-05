import HadwigerRamsey4Col.RealizationC4Pattern
import HadwigerRamsey4Col.RealizationDensities
import HadwigerRamsey4Col.RealizationConvergenceBridge

open MeasureTheory Filter Set Finset HadwigerRamsey
open scoped BigOperators Topology Classical

namespace HadwigerRamsey4Col.Realization

lemma finiteMarkMass_eq_classMass {n k : ℕ} (τ : Fin n → Fin k) (i : Fin k) :
    finiteMarkMass τ i = classMass τ i := by
  rw [finiteMarkMass, Finset.expect_eq_sum_div_card, Finset.sum_boole]
  simp only [Finset.card_univ, Fintype.card_fin, classMass]

/-- Convergence of all finite marked coloured patterns implies common cut
convergence whenever the marks carry increasingly accurate finite matrix
approximations of the target tuple. One coupling works for all colours. -/
theorem patterns_imply_common_cut {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r : ℕ} (c₀ : Fin r)
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (W : Fin r → Graphon α μ)
    (k : ℕ → ℕ) (marks : ∀ l, α → Fin (k l))
    (hmeas : ∀ l, Measurable (marks l))
    (B : ∀ l, Fin r → Fin (k l) → Fin (k l) → ℝ)
    (hsymm : ∀ l c i j, B l c i j = B l c j i)
    (hbounds : ∀ l c i j, B l c i j ∈ Icc (0 : ℝ) 1)
    (labels : ∀ l n, Fin (N n) → Fin (k l))
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (happrox : ∀ c, Tendsto (fun l => Graphon.cutNormDiff (W c)
      (markedGraphon (B l c) (hsymm l c) (hbounds l c) (marks l) (hmeas l)))
      atTop (𝓝 0))
    (htests : ∀ l, ∀ P : Pattern r (k l),
      Tendsto (fun n => finitePatternDensity P (G n) (labels l n)) atTop
        (𝓝 (markedDensity P W (fun i => (marks l) ⁻¹' {i})))) :
    FiniteCommonCutConverges μ (fun n c => Graphon.adjIndicator (G n c))
      (fun n c => adjacencyMatrix_symm (G n c))
      (fun n c => adjacencyMatrix_bounds (G n c)) W := by
  apply finiteCommonCutConverges_of_C4
    (fun n c => Graphon.adjIndicator (G n c))
    (fun n c => adjacencyMatrix_symm (G n c))
    (fun n c => adjacencyMatrix_bounds (G n c))
    W k marks hmeas B hsymm hbounds labels
  · filter_upwards [hN] with n hn
    exact ⟨⟨0, hn⟩⟩
  · exact happrox
  · intro l i
    simpa only [finiteMarkMass_eq_classMass] using
      classMass_tendsto_of_patterns c₀ N G (labels l) W
        (fun i => (marks l) ⁻¹' {i})
        (fun i => hmeas l (measurableSet_singleton i)) (htests l) i
  · intro l c
    let a : Fin (k l) := marks l (Classical.choice (nonempty_of_isProbabilityMeasure μ))
    refine ⟨residualC4Integral (W c) (B l c) (marks l), ?_, ?_⟩
    · exact finiteC4_tendsto_of_patterns c a N G (labels l) W (marks l) (hmeas l)
        (htests l) (B l c) (hsymm l c)
    · exact residualC4Integral_le (W c) (B l c) (hsymm l c) (hbounds l c)
        (marks l) (hmeas l)

end HadwigerRamsey4Col.Realization
