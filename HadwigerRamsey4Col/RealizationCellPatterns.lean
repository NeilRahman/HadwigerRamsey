import HadwigerRamsey4Col.RealizationCells
import HadwigerRamsey4Col.RealizationDefinitions
import HadwigerRamsey4Col.RealizationProbabilityStatistics

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set Finset

namespace HadwigerRamsey4Col.Realization

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- Uniform-cell conditional sampling has exactly the fractional marked integral. -/
theorem fractionalPatternAverage_cellConditionalMeasure {m n : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (hn : 0 < n) (cell : α → Fin n) (hcell : Measurable cell)
    (hcellmass : ∀ v, μ.real (cell ⁻¹' {v}) = 1/(n : ℝ))
    (mark : α → K) (hmark : Measurable mark)
    (w : (Fin m → Fin n) → ℝ) (a : Fin m → K) :
    fractionalPatternAverage (fun v => (cellConditionalMeasure μ cell v).map mark) w a =
      ∫ x : Fin m → α,
        (∏ i, (mark ⁻¹' {a i}).indicator (fun _ => (1 : ℝ)) (x i)) *
          w (fun i => cell (x i)) ∂Measure.pi (fun _ => μ) := by
  rw [integral_cell_expansion μ cell hcell (fun i => mark ⁻¹' {a i})
    (fun i => hmark (measurableSet_singleton _)) w]
  unfold fractionalPatternAverage
  simp_rw [cellConditionalMeasure_map_singleton μ cell hcell hcellmass mark hmark]
  rw [Finset.sum_div]
  refine Finset.sum_congr ?_ ?_
  · ext f
    simp
  intro f hf
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [Set.inter_comm (cell ⁻¹' {_})]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- For kernels constant on vertex cells, the marked graphon integral is the
finite-cell weighted integral, including maps which identify test vertices. -/
theorem markedDensity_cell_integral {r k n : ℕ} (P : Pattern r k)
    (G : Fin r → SimpleGraph (Fin n)) (U : Fin r → Graphon α μ)
    (cell : α → Fin n)
    (hU : ∀ c, ∀ᵐ p ∂μ.prod μ,
      (U c).toAEEqFun p = Graphon.adjIndicator (G c) (cell p.1) (cell p.2))
    (A : Fin k → Set α) :
    markedDensity P U A = ∫ x : Fin P.1 → α,
      (∏ i, (A (P.label i)).indicator (fun _ => (1 : ℝ)) (x i)) *
        finitePatternWeight P G (fun i => cell (x i)) ∂Measure.pi (fun _ => μ) := by
  have he : ∀ e ∈ P.graph.edgeFinset, ∀ᵐ x : Fin P.1 → α ∂Measure.pi (fun _ => μ),
      (U (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
      Graphon.adjIndicator (G (P.colour e)) (cell (x (Quot.out e).1))
        (cell (x (Quot.out e).2)) := by
    intro e he
    exact (pair_measurePreserving (μ := μ) (Quot.out e).1 (Quot.out e).2
      (Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))).quasiMeasurePreserving.ae
        (hU (P.colour e))
  have hall : ∀ᵐ x : Fin P.1 → α ∂Measure.pi (fun _ => μ),
      ∀ e ∈ P.graph.edgeFinset,
      (U (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
      Graphon.adjIndicator (G (P.colour e)) (cell (x (Quot.out e).1))
        (cell (x (Quot.out e).2)) := by
    simpa only [ae_all_iff] using he
  apply integral_congr_ae
  filter_upwards [hall] with x hx
  congr 1
  exact Finset.prod_congr rfl hx

/-- Exact bridge between the fractional finite-graph statistic and the marked
density of its graphon in any uniform-cell realization. -/
theorem fractionalPatternAverage_eq_markedDensity {r k n : ℕ}
    (P : Pattern r k) (hn : 0 < n)
    (G : Fin r → SimpleGraph (Fin n)) (U : Fin r → Graphon α μ)
    (cell : α → Fin n) (hcell : Measurable cell)
    (hcellmass : ∀ v, μ.real (cell ⁻¹' {v}) = 1/(n : ℝ))
    (hU : ∀ c, ∀ᵐ p ∂μ.prod μ,
      (U c).toAEEqFun p = Graphon.adjIndicator (G c) (cell p.1) (cell p.2))
    (mark : α → Fin k) (hmark : Measurable mark) :
    fractionalPatternAverage (fun v => (cellConditionalMeasure μ cell v).map mark)
      (finitePatternWeight P G) P.label =
      markedDensity P U (fun i => mark ⁻¹' {i}) := by
  rw [markedDensity_cell_integral μ P G U cell hU]
  exact fractionalPatternAverage_cellConditionalMeasure μ hn cell hcell hcellmass mark hmark
    (finitePatternWeight P G) P.label

end HadwigerRamsey4Col.Realization
