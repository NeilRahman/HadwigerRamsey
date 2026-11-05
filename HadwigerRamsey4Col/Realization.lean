import HadwigerRamsey4Col.RealizationProbabilityMarked
import HadwigerRamsey4Col.RealizationCellPatterns

open scoped BigOperators Topology Classical
open MeasureTheory Filter Finset Set

namespace HadwigerRamsey4Col.Realization

/-- Common cut-norm convergence of coloured step graphons permits one choice
of a point in every vertex cell which simultaneously realizes all coloured
finite tests for every marking in a countable family of measurable markings. -/
theorem exists_realization_all_marked_patterns {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (cell : ∀ n, α → Fin (N n)) (hcell : ∀ n, Measurable (cell n))
    (hcellmass : ∀ n v, μ.real ((cell n) ⁻¹' {v}) = 1/(N n : ℝ))
    (U : ℕ → Fin r → Graphon α μ) (W : Fin r → Graphon α μ)
    (hU : ∀ n c, ∀ᵐ p ∂μ.prod μ,
      (U n c).toAEEqFun p = Graphon.adjIndicator (G n c) (cell n p.1) (cell n p.2))
    (hcut : ∀ c, Tendsto (fun n => Graphon.cutNormDiff (U n c) (W c)) atTop (𝓝 0))
    (k : ℕ → ℕ) (π : ∀ j, α → Fin (k j)) (hπ : ∀ j, Measurable (π j)) :
    ∃ x : ∀ n, Fin (N n) → α, (∀ n v, cell n (x n v) = v) ∧
      ∀ j (P : Pattern r (k j)),
        Tendsto (fun n => finitePatternDensity P (G n) (π j ∘ x n)) atTop
          (𝓝 (markedDensity P W (fun i => (π j) ⁻¹' {i}))) := by
  let T := Σ j : ℕ, Pattern r (k j)
  have : Countable T := by dsimp [T]; infer_instance
  have : Nonempty T := by
    refine ⟨⟨0, ⟨0, ⊥, ?_, ?_⟩⟩⟩
    · exact fun e => isEmptyElim e
    · exact Fin.elim0
  let ν := fun n v => cellConditionalMeasure μ (cell n) v
  have hν (n : ℕ) (v : Fin (N n)) : IsProbabilityMeasure (ν n v) :=
    cellConditionalMeasure_probability μ (hNpos n) (cell n) (hcellmass n) v
  have hsupport (n : ℕ) : ∀ᵐ x ∂Measure.pi (ν n), ∀ v, cell n (x v) = v := by
    rw [ae_all_iff]
    intro v
    exact (measurePreserving_eval (ν n) v).quasiMeasurePreserving.ae
      (cellConditionalMeasure_support μ (cell n) (hcell n) v)
  have htargets (t : T) :
      Tendsto (fun n => fractionalPatternAverage
        (fun v => (ν n v).map (π t.1)) (finitePatternWeight t.2 (G n)) t.2.label) atTop
        (𝓝 (markedDensity t.2 W (fun i => (π t.1) ⁻¹' {i}))) := by
    have hh := markedDensity_tendsto t.2 U W (fun i => (π t.1) ⁻¹' {i})
      (fun i => (hπ t.1) (measurableSet_singleton i)) hcut
    apply hh.congr'
    exact Eventually.of_forall (fun n =>
      (fractionalPatternAverage_eq_markedDensity μ t.2 (hNpos n) (G n) (U n)
        (cell n) (hcell n) (hcellmass n) (hU n) (π t.1) (hπ t.1)).symm)
  obtain ⟨x, hx, hpatterns⟩ := exists_countable_marked_pattern_realization (ι := T)
    N hN ν (fun t => t.2.1) (fun t => k t.1) (fun t => π t.1) (fun t => hπ t.1)
    (fun n t => finitePatternWeight t.2 (G n))
    (fun n t => finitePatternWeight_bounds t.2 (G n))
    (fun t => t.2.label) (fun t => markedDensity t.2 W (fun i => (π t.1) ⁻¹' {i}))
    (fun n x => ∀ v, cell n (x v) = v) hsupport htargets
  exact ⟨x, hx, fun j P => hpatterns ⟨j,P⟩⟩

end HadwigerRamsey4Col.Realization
