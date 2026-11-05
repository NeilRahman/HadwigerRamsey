import HadwigerRamsey4Col.RealizationConvergenceBridge

open MeasureTheory Filter Set
open scoped Topology

namespace HadwigerRamsey4Col.Realization

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A common alignment supplies a genuine coupling by recording its two
measure-preserving coordinate maps. -/
noncomputable def ProbabilityCoupling.ofMaps (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (f : Ω → α) (hf : MeasurePreserving f ρ μ)
    (g : Ω → β) (hg : MeasurePreserving g ρ ν) : ProbabilityCoupling μ ν where
  law := ρ.map (fun x => (f x, g x))
  probability := Measure.isProbabilityMeasure_map (hf.measurable.prodMk hg.measurable).aemeasurable
  fst_mp := ⟨measurable_fst, by
    rw [Measure.map_map measurable_fst (hf.measurable.prodMk hg.measurable)]
    exact hf.map_eq⟩
  snd_mp := ⟨measurable_snd, by
    rw [Measure.map_map measurable_snd (hf.measurable.prodMk hg.measurable)]
    exact hg.map_eq⟩

/-- Passing from a common alignment to its coupling preserves the cut cost
exactly, for every pair of kernels simultaneously. -/
theorem ProbabilityCoupling.ofMaps_cost (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (f : Ω → α) (hf : MeasurePreserving f ρ μ)
    (g : Ω → β) (hg : MeasurePreserving g ρ ν)
    (U : Graphon α μ) (W : Graphon β ν) :
    (ProbabilityCoupling.ofMaps ρ f hf g hg).cost U W =
      Graphon.cutNormDiff (Graphon.pullback U f hf) (Graphon.pullback W g hg) := by
  let C := ProbabilityCoupling.ofMaps ρ f hf g hg
  have hpair : MeasurePreserving (fun x => (f x, g x)) ρ C.law :=
    ⟨hf.measurable.prodMk hg.measurable, rfl⟩
  change Graphon.cutNormDiff (Graphon.pullback U Prod.fst C.fst_mp)
    (Graphon.pullback W Prod.snd C.snd_mp) = _
  rw [← Graphon.cutNormDiff_pullback_eq_measurePreserving
    (Graphon.pullback U Prod.fst C.fst_mp) (Graphon.pullback W Prod.snd C.snd_mp)
    (fun x => (f x, g x)) hpair]
  rw [Graphon.pullback_pullback, Graphon.pullback_pullback]
  rfl

/-- Convergence after common measure-preserving alignments implies the common
coupling formulation used for measurable-partition realization. -/
theorem commonCutConverges_of_common_maps {r : ℕ} {V Ξ : ℕ → Type*}
    [∀ n, MeasurableSpace (V n)] [∀ n, MeasurableSpace (Ξ n)]
    (νs : ∀ n, Measure (V n)) [∀ n, IsProbabilityMeasure (νs n)]
    (ρs : ∀ n, Measure (Ξ n)) [∀ n, IsProbabilityMeasure (ρs n)]
    (U : ∀ n, Fin r → Graphon (V n) (νs n)) (W : Fin r → Graphon α μ)
    (f : ∀ n, Ξ n → V n) (hf : ∀ n, MeasurePreserving (f n) (ρs n) (νs n))
    (g : ∀ n, Ξ n → α) (hg : ∀ n, MeasurePreserving (g n) (ρs n) μ)
    (hcut : ∀ c, Tendsto (fun n => Graphon.cutNormDiff
      (Graphon.pullback (U n c) (f n) (hf n)) (Graphon.pullback (W c) (g n) (hg n)))
      atTop (𝓝 0)) :
    CommonCutConverges νs μ U W := by
  intro ε hε
  have he : ∀ᶠ n in atTop, ∀ c, Graphon.cutNormDiff
      (Graphon.pullback (U n c) (f n) (hf n))
      (Graphon.pullback (W c) (g n) (hg n)) < ε := by
    rw [Filter.eventually_all]
    intro c
    exact (tendsto_order.mp (hcut c)).2 ε hε
  filter_upwards [he] with n hn
  refine ⟨ProbabilityCoupling.ofMaps (ρs n) (f n) (hf n) (g n) (hg n), fun c => ?_⟩
  rw [ProbabilityCoupling.ofMaps_cost]
  exact hn c

end HadwigerRamsey4Col.Realization
