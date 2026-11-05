import HadwigerRamsey4Col.RealizationDefinitions

open MeasureTheory Set Filter Finset
open scoped BigOperators Topology Classical

namespace HadwigerRamsey4Col.Realization

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Marked coloured homomorphism densities are preserved by a common
measure-preserving pullback, including non-injective maps of the carriers. -/
theorem markedDensity_pullback {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (φ : β → α) (hφ : MeasurePreserving φ ν μ) :
    markedDensity P (fun c => Graphon.pullback (W c) φ hφ) (fun i => φ ⁻¹' A i) =
      markedDensity P W A := by
  let f : (Fin P.1 → α) → ℝ := fun x =>
    (∏ u, (A (P.label u)).indicator (fun _ => (1 : ℝ)) (x u)) *
    ∏ e ∈ P.graph.edgeFinset,
      (W (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
  have hf : Measurable f := by
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro u _
      exact (measurable_const.indicator (hA (P.label u))).comp (measurable_pi_apply u)
    · apply Finset.measurable_prod
      intro e _
      exact (W (P.colour e)).toAEEqFun.stronglyMeasurable.measurable.comp
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hmp : MeasurePreserving (fun x : Fin P.1 → β => φ ∘ x)
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ => μ)) :=
    measurePreserving_pi (fun _ => ν) (fun _ => μ) (fun _ => hφ)
  have he : ∀ᵐ x : Fin P.1 → β ∂Measure.pi (fun _ => ν),
      ∀ e ∈ P.graph.edgeFinset,
        (Graphon.pullback (W (P.colour e)) φ hφ).toAEEqFun
          (x (Quot.out e).1, x (Quot.out e).2) =
        (W (P.colour e)).toAEEqFun (φ (x (Quot.out e).1), φ (x (Quot.out e).2)) := by
    rw [Filter.eventually_all_finset]
    intro e he
    exact (pair_measurePreserving (μ := ν) (Quot.out e).1 (Quot.out e).2
      (Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))).quasiMeasurePreserving.ae
        (Graphon.pullback_ae (W (P.colour e)) φ hφ)
  calc
    markedDensity P (fun c => Graphon.pullback (W c) φ hφ) (fun i => φ ⁻¹' A i) =
        ∫ x : Fin P.1 → β, f (φ ∘ x) ∂Measure.pi (fun _ => ν) := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      unfold f
      congr 1
      exact Finset.prod_congr rfl hx
    _ = ∫ x, f x ∂Measure.pi (fun _ => μ) := by
      rw [← hmp.map_eq]
      exact (integral_map hmp.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ = markedDensity P W A := rfl

/-- The marked counting limit on varying coupling spaces. The target carrier
and its marks remain fixed, while each source may use a different coupling. -/
theorem markedDensity_tendsto_varying
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ρ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (ρ n)]
    {r k : ℕ} (P : Pattern r k)
    (U : ∀ n, Fin r → Graphon (Ω n) (ρ n)) (W : Fin r → Graphon α μ)
    (φ : ∀ n, Ω n → α) (hφ : ∀ n, MeasurePreserving (φ n) (ρ n) μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hcut : ∀ c, Tendsto (fun n => Graphon.cutNormDiff (U n c)
      (Graphon.pullback (W c) (φ n) (hφ n))) atTop (𝓝 0)) :
    Tendsto (fun n => markedDensity P (U n) (fun i => (φ n) ⁻¹' A i))
      atTop (𝓝 (markedDensity P W A)) := by
  have hmass (n : ℕ) (i : Fin k) : (ρ n).real ((φ n) ⁻¹' A i) = μ.real (A i) := by
    exact congrArg ENNReal.toReal ((hφ n).measure_preimage (hA i).nullMeasurableSet)
  by_cases hpos : ∀ u : Fin P.1, 0 < μ.real (A (P.label u))
  · have hbound (n : ℕ) := vertex_weighted_counting P.graph.edgeFinset
      (fun e => U n (P.colour e))
      (fun e => Graphon.pullback (W (P.colour e)) (φ n) (hφ n))
      (fun e he => Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
      (fun u => (φ n) ⁻¹' A (P.label u))
      (fun u => (hφ n).measurable (hA (P.label u)))
      (fun u => by rw [hmass]; exact hpos u)
    have hbound' (n : ℕ) :
        |markedDensity P (U n) (fun i => (φ n) ⁻¹' A i) - markedDensity P W A| ≤
        (∑ e ∈ P.graph.edgeFinset,
          Graphon.cutNormDiff (U n (P.colour e))
            (Graphon.pullback (W (P.colour e)) (φ n) (hφ n))) /
          ∏ u, μ.real (A (P.label u)) := by
      have hh := hbound n
      change |markedDensity P (U n) (fun i => (φ n) ⁻¹' A i) -
        markedDensity P (fun c => Graphon.pullback (W c) (φ n) (hφ n))
          (fun i => (φ n) ⁻¹' A i)| ≤ _ at hh
      simpa only [markedDensity_pullback P W A hA, hmass] using hh
    have hlim : Tendsto (fun n => (∑ e ∈ P.graph.edgeFinset,
        Graphon.cutNormDiff (U n (P.colour e))
          (Graphon.pullback (W (P.colour e)) (φ n) (hφ n))) /
          ∏ u, μ.real (A (P.label u))) atTop (𝓝 0) := by
      simpa using (tendsto_finsetSum P.graph.edgeFinset
        (fun e _ => hcut (P.colour e))).div_const (∏ u, μ.real (A (P.label u)))
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using squeeze_zero
      (fun n => abs_nonneg (markedDensity P (U n) (fun i => (φ n) ⁻¹' A i) -
        markedDensity P W A)) hbound' hlim
  · push Not at hpos
    obtain ⟨u, hu⟩ := hpos
    have hz : μ (A (P.label u)) = 0 := (measureReal_eq_zero_iff (μ := μ)).mp
      (le_antisymm hu measureReal_nonneg)
    have hzn (n : ℕ) : ρ n ((φ n) ⁻¹' A (P.label u)) = 0 :=
      ((hφ n).measure_preimage (hA (P.label u)).nullMeasurableSet).trans hz
    have hzN (n : ℕ) : markedDensity P (U n) (fun i => (φ n) ⁻¹' A i) = 0 :=
      markedDensity_zero_of_null P (U n) (fun i => (φ n) ⁻¹' A i) u (hzn n)
    simp only [markedDensity_zero_of_null P _ A u hz, hzN]
    exact tendsto_const_nhds

end HadwigerRamsey4Col.Realization
