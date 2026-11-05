import HadwigerRamsey4Col.RealizationCouplingInput
import HadwigerRamsey4Col.RealizationInducedCut
import HadwigerRamsey4Col.RealizationPartitions

open scoped Classical Topology
open MeasureTheory ProbabilityTheory Filter Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

set_option backward.isDefEq.respectTransparency false

namespace HadwigerRamsey4Col.Realization

/-- The conclusions of measurable-partition realization. The diagonal block
uses ordinary induced-graph density, and each nonempty union converges in the
common coloured cut metric with normalized restricted measure. -/
def RealizesPartition {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (W : Fin r → Graphon α μ) (A : Fin k → Set α)
    (labels : ∀ n, Fin (N n) → Fin k) : Prop :=
  (∀ i, Tendsto (fun n => classMass (labels n) i) atTop (𝓝 (μ.real (A i)))) ∧
  (∀ c i j, Tendsto (fun n => blockDensity (G n c) (labels n) i j) atTop
    (𝓝 ((W c).toSymmKernel.rectIntegral (A i) (A j) /
      (μ.real (A i) * μ.real (A j))))) ∧
  ∀ J : Finset (Fin k), J.Nonempty →
    ∃ hJ : μ (⋃ i ∈ J, A i) ≠ 0,
      letI : IsProbabilityMeasure (cond μ (⋃ i ∈ J, A i)) := cond_isProbabilityMeasure hJ
      let S := fun n => Finset.univ.filter (fun v => labels n v ∈ (J : Set (Fin k)))
      FiniteGraphCommonCutConverges (cond μ (⋃ i ∈ J, A i))
        (fun n => (S n).card) (fun n c => selectedGraph (G n c) (S n))
        (fun c => restrictGraphon (W c) (⋃ i ∈ J, A i))

end Realization

open Realization

/-- **Lemma 7 of `comptransfer.tex`.** Every fixed finite measurable partition
into positive-measure sets is realized by vertex partitions, with the correct
part sizes, ordinary edge densities, and common-coloured cut limits on every
nonempty union of parts.

The statement holds on any probability space, hence in particular on the
unit interval with Lebesgue measure. No compatibility assumptions on the
colour graphs or on the sum of the kernels are needed; this stronger form
includes the manuscript's edge-coloured graphs and coloured graphons. -/
theorem lemma7 {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r k : ℕ} (hr : 2 ≤ r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (hconv : FiniteGraphCommonCutConverges μ N G W)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : (⋃ i, A i) = Set.univ) (hpos : ∀ i, 0 < μ.real (A i)) :
    ∃ labels : ∀ n, Fin (N n) → Fin k, RealizesPartition μ N G W A labels := by
  obtain ⟨original, horiginal, hfibre⟩ := exists_partition_mark A hA hdisjoint hcover
  let c₀ : Fin r := ⟨0, by omega⟩
  let approx := commonFiniteApproximationSequence W original horiginal
  let sizes : ℕ → ℕ := fun j => match j with
    | 0 => k
    | l + 1 => (approx l).n
  let marks : ∀ j, α → Fin (sizes j) := fun j => match j with
    | 0 => original
    | l + 1 => (approx l).mark
  have hmarks (j : ℕ) : Measurable (marks j) := by
    cases j with
    | zero => exact horiginal
    | succ l => exact (approx l).measurable_mark
  obtain ⟨samples, htests⟩ := exists_realization_of_finite_common_cut μ N hN G W hconv
    sizes marks hmarks
  have hOriginal : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (original ∘ samples n)) atTop
        (𝓝 (markedDensity P W (fun i => original ⁻¹' {i}))) := htests 0
  have hApprox : ∀ l, ∀ P : Pattern r ((approx l).n),
      Tendsto (fun n => finitePatternDensity P (G n) ((approx l).mark ∘ samples n)) atTop
        (𝓝 (markedDensity P W (fun i => (approx l).mark ⁻¹' {i}))) := fun l => htests (l+1)
  let labels : ∀ n, Fin (N n) → Fin k := fun n => original ∘ samples n
  have hOriginalA : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (labels n)) atTop
        (𝓝 (markedDensity P W A)) := by
    intro P
    simpa only [hfibre] using hOriginal P
  refine ⟨labels, ?_, ?_, ?_⟩
  · intro i
    exact classMass_tendsto_of_patterns c₀ N G labels W A hA hOriginalA i
  · intro c i j
    exact blockDensity_tendsto_rectIntegral_of_order_tendsto N hN G labels W A hA hpos
      hOriginalA c i j
  · intro J hJ
    have hpositive : 0 < μ.real (original ⁻¹' (J : Set (Fin k))) :=
      partition_mark_union_pos original (by simpa only [hfibre] using hpos) J hJ
    have hneq : μ (original ⁻¹' (J : Set (Fin k))) ≠ 0 := by
      intro hz
      have : μ.real (original ⁻¹' (J : Set (Fin k))) = 0 := by simp [measureReal_def, hz]
      linarith
    have hunion := partition_mark_union A original hfibre J
    have hJpos : μ (⋃ i ∈ J, A i) ≠ 0 := by rwa [← hunion]
    refine ⟨hJpos, ?_⟩
    letI : IsProbabilityMeasure (cond μ (original ⁻¹' (J : Set (Fin k)))) :=
      cond_isProbabilityMeasure hneq
    have hcut := induced_common_cut_of_marked_patterns c₀ N hN G W original horiginal
      samples hOriginal hApprox (J : Set (Fin k)) hpositive
    have htransfer (T : Set α) (hT : T = original ⁻¹' (J : Set (Fin k)))
        (hTpos : μ T ≠ 0) :
        letI : IsProbabilityMeasure (cond μ T) := cond_isProbabilityMeasure hTpos
        let S := fun n => Finset.univ.filter (fun v => labels n v ∈ (J : Set (Fin k)))
        FiniteGraphCommonCutConverges (cond μ T) (fun n => (S n).card)
          (fun n c => selectedGraph (G n c) (S n)) (fun c => restrictGraphon (W c) T) := by
      subst T
      unfold FiniteGraphCommonCutConverges
      convert hcut using 1
      dsimp only [labels, Function.comp_apply]
      congr!
      subst_vars
      apply congrArg Finset.card
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, labels, Function.comp_apply]
    exact htransfer _ hunion.symm hJpos

end HadwigerRamsey4Col
