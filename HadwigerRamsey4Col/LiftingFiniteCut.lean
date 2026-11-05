import HadwigerRamsey4Col.RealizationCouplingInput

open scoped Classical Topology BigOperators
open MeasureTheory Filter Set Finset
open HadwigerRamsey4Col.Realization

set_option backward.isDefEq.respectTransparency false

namespace HadwigerRamsey4Col.Lifting

noncomputable def finiteGraphon {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) :
    Graphon (Fin n) (uniformFiniteMeasure (Fin n)) :=
  markedGraphon (Graphon.adjIndicator G) (adjIndicator_symm_all G)
    (adjIndicator_bounds_all G) id measurable_id

lemma uniformFiniteMeasure_finset {n : ℕ} [Nonempty (Fin n)] (A : Finset (Fin n)) :
    (uniformFiniteMeasure (Fin n)).real (A : Set (Fin n)) = (A.card : ℝ)/(n : ℝ) := by
  have h := integral_uniform_eq_expect (ν := uniformFiniteMeasure (Fin n))
    uniformFiniteMeasure_singleton ((A : Set (Fin n)).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator (A.finite_toSet.measurableSet), setIntegral_const] at h
  simpa [Finset.expect_eq_sum_div_card, Set.indicator_apply] using h

lemma finiteGraphon_rectIntegral {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) :
    (finiteGraphon G).toSymmKernel.rectIntegral (A : Set (Fin n)) (B : Set (Fin n)) =
      ((G.interedges A B).card : ℝ)/(n : ℝ)^2 := by
  let ν := uniformFiniteMeasure (Fin n)
  have hmass (p : Fin n × Fin n) : (ν.prod ν).real {p} = 1/(n : ℝ)^2 := by
    rw [← Set.singleton_prod_singleton, measureReal_prod_prod,
      uniformFiniteMeasure_singleton, uniformFiniteMeasure_singleton]
    simp only [Fintype.card_fin]
    ring
  unfold SymmKernel.rectIntegral
  rw [← integral_indicator (A.finite_toSet.measurableSet.prod B.finite_toSet.measurableSet),
    integral_fintype Integrable.of_finite]
  have heq (p : Fin n × Fin n) :
      (ν.prod ν).real {p} • ((A : Set (Fin n)) ×ˢ (B : Set (Fin n))).indicator
        (fun p => (finiteGraphon G).toAEEqFun p) p =
      (if p ∈ G.interedges A B then (1 : ℝ) else 0)/(n : ℝ)^2 := by
    rw [smul_eq_mul, hmass]
    have hraw := markedGraphon_uniform_apply (ν := ν) uniformFiniteMeasure_singleton
      (Graphon.adjIndicator G) (adjIndicator_symm_all G) (adjIndicator_bounds_all G)
      id measurable_id p.1 p.2
    change (finiteGraphon G).toAEEqFun p = Graphon.adjIndicator G p.1 p.2 at hraw
    by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;>
      by_cases hadj : G.Adj p.1 p.2 <;>
      simp [Set.indicator_apply, Set.mem_prod, ha, hb, hraw, Graphon.adjIndicator,
        hadj, SimpleGraph.mem_interedges_iff]
  change (∑ p : Fin n × Fin n, (ν.prod ν).real {p} •
    ((A : Set (Fin n)) ×ˢ (B : Set (Fin n))).indicator
      (fun p => (finiteGraphon G).toAEEqFun p) p) = _
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_boole]
  simp

lemma finiteGraphon_cutIntegral {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) :
    (finiteGraphon G).toSymmKernel.rectIntegral (A : Set (Fin n)) (A : Set (Fin n))ᶜ =
      ((G.interedges A (Finset.univ \ A)).card : ℝ)/(n : ℝ)^2 := by
  have hset : ((Finset.univ \ A : Finset (Fin n)) : Set (Fin n)) = (A : Set (Fin n))ᶜ := by
    ext v
    simp
  rw [← hset]
  exact finiteGraphon_rectIntegral G A (Finset.univ \ A)

lemma rectIntegral_pullback_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν)
    {S T : Set β} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (Graphon.pullback W φ hφ).toSymmKernel.rectIntegral (φ ⁻¹' S) (φ ⁻¹' T) =
      W.toSymmKernel.rectIntegral S T := by
  have hstep : (Graphon.pullback W φ hφ).toSymmKernel.rectIntegral (φ ⁻¹' S) (φ ⁻¹' T) =
      ∫ p in (φ ⁻¹' S) ×ˢ (φ ⁻¹' T), W.toAEEqFun (φ p.1,φ p.2) ∂μ.prod μ := by
    unfold SymmKernel.rectIntegral
    exact integral_congr_ae (ae_restrict_of_ae (Graphon.pullback_ae W φ hφ))
  have hΦ : MeasurePreserving (Prod.map φ φ)
      ((μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T)))
      ((ν.restrict S).prod (ν.restrict T)) :=
    (hφ.restrict_preimage hS).prod (hφ.restrict_preimage hT)
  rw [hstep]
  unfold SymmKernel.rectIntegral
  rw [← Measure.prod_restrict, ← Measure.prod_restrict]
  change (∫ p, W.toAEEqFun (Prod.map φ φ p) ∂
    (μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T))) = _
  calc
    _ = ∫ q, W.toAEEqFun q ∂Measure.map (Prod.map φ φ)
        ((μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T))) :=
      (integral_map hΦ.measurable.aemeasurable W.toAEEqFun.stronglyMeasurable.aestronglyMeasurable).symm
    _ = _ := by rw [hΦ.map_eq]

end HadwigerRamsey4Col.Lifting
