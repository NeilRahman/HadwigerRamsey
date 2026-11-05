import HadwigerRamsey4Col.RealizationPatternsToCut
import HadwigerRamsey4Col.RealizationInduced
import HadwigerRamsey4Col.RealizationCommonApproximation

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped BigOperators Topology Classical

namespace HadwigerRamsey4Col.Realization

/-- Realizing the original marking and the countable common approximation
marks realizes every positive-mass induced union in the common coloured cut
metric. The selected graph is the actual induced graph, canonically numbered. -/
theorem induced_common_cut_of_marked_patterns
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {r k : ℕ} (c₀ : Fin r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (original : α → Fin k) (horiginal : Measurable original)
    (samples : ∀ n, Fin (N n) → α)
    (htestsOriginal : ∀ Q : Pattern r k,
      Tendsto (fun n => finitePatternDensity Q (G n) (original ∘ samples n)) atTop
        (𝓝 (markedDensity Q W (fun i => original ⁻¹' {i}))))
    (htestsApprox : ∀ l, ∀ Q : Pattern r
        ((commonFiniteApproximationSequence W original horiginal l).n),
      Tendsto (fun n => finitePatternDensity Q (G n)
        ((commonFiniteApproximationSequence W original horiginal l).mark ∘ samples n)) atTop
        (𝓝 (markedDensity Q W (fun i =>
          (commonFiniteApproximationSequence W original horiginal l).mark ⁻¹' {i}))))
    (J : Set (Fin k)) (hpos : 0 < μ.real (original ⁻¹' J))
    [IsProbabilityMeasure (cond μ (original ⁻¹' J))] :
    let S := fun n => Finset.univ.filter (fun v => original (samples n v) ∈ J)
    FiniteCommonCutConverges (cond μ (original ⁻¹' J))
      (fun n c => Graphon.adjIndicator (selectedGraph (G n c) (S n)))
      (fun n c => adjacencyMatrix_symm (selectedGraph (G n c) (S n)))
      (fun n c => adjacencyMatrix_bounds (selectedGraph (G n c) (S n)))
      (fun c => restrictGraphon (W c) (original ⁻¹' J)) := by
  let S := fun n => Finset.univ.filter (fun v => original (samples n v) ∈ J)
  let P := commonFiniteApproximationSequence W original horiginal
  have hSmeas : MeasurableSet (original ⁻¹' J) := horiginal MeasurableSet.of_discrete
  have hmass := selected_mass_tendsto c₀ N G (fun n => original ∘ samples n)
    W original horiginal J htestsOriginal
  have horder : Tendsto (fun n => (S n).card) atTop atTop :=
    selected_order_tendsto_of_order_tendsto N hN (fun n => original ∘ samples n)
      J hpos hmass
  have hselected (l : ℕ) :=
    selected_patterns_tendsto_of_refinement_of_order_tendsto c₀ N hN G
      (fun n => original ∘ samples n) (fun n => (P l).mark ∘ samples n)
      W original (P l).mark (P l).measurable_mark (P l).label
      (fun n v => (P l).refines (samples n v)) (P l).refines J hpos (htestsApprox l)
  have happrox (c : Fin r) :
      Tendsto (fun l => Graphon.cutNormDiff (restrictGraphon (W c) (original ⁻¹' J))
        (markedGraphon (μ := cond μ (original ⁻¹' J)) ((P l).matrix c)
          ((P l).matrix_symm c) ((P l).matrix_bounds c) (P l).mark (P l).measurable_mark))
        atTop (𝓝 0) := by
    have hglobal := commonFiniteApproximationSequence_tendsto W original horiginal c
    have hlim : Tendsto (fun l => Graphon.cutNormDiff (W c) ((P l).graphon c) /
        (μ.real (original ⁻¹' J)) ^ 2) atTop (𝓝 0) := by
      simpa only [zero_div] using hglobal.div_const ((μ.real (original ⁻¹' J)) ^ 2)
    apply squeeze_zero (fun l => Graphon.cutNormDiff_nonneg _ _) (fun l => ?_) hlim
    have hb := restrictGraphon_cutNormDiff_le (W c) ((P l).graphon c)
      (original ⁻¹' J) hSmeas
    simpa only [CommonFiniteApproximation.graphon, restrictGraphon_markedGraphon] using hb
  exact patterns_imply_common_cut c₀ (fun n => (S n).card)
    (fun n c => selectedGraph (G n c) (S n))
    (fun c => restrictGraphon (W c) (original ⁻¹' J))
    (fun l => (P l).n) (fun l => (P l).mark) (fun l => (P l).measurable_mark)
    (fun l => (P l).matrix) (fun l => (P l).matrix_symm) (fun l => (P l).matrix_bounds)
    (fun l n => ((P l).mark ∘ samples n) ∘ selectedEmbedding (S n))
    ((horder.eventually_ge_atTop 1).mono fun n hn => by omega) happrox hselected

end HadwigerRamsey4Col.Realization
