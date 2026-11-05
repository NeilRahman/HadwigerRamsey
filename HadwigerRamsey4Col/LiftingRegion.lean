import HadwigerRamsey4Col.LiftingRealization

open scoped Classical Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

set_option backward.isDefEq.respectTransparency false

namespace HadwigerRamsey4Col.Realization

/-- Simultaneously realize one marking and all its finite graphon approximation
refinements. Null marking classes are permitted. -/
theorem exists_marked_realization {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (hconv : FiniteGraphCommonCutConverges μ N G W)
    (original : α → Fin k) (horiginal : Measurable original) :
    ∃ samples : ∀ n, Fin (N n) → α,
      (∀ P : Pattern r k, Tendsto (fun n => finitePatternDensity P (G n)
        (original ∘ samples n)) atTop
        (𝓝 (markedDensity P W (fun i => original ⁻¹' {i})))) ∧
      ∀ l, ∀ P : Pattern r ((commonFiniteApproximationSequence W original horiginal l).n),
        Tendsto (fun n => finitePatternDensity P (G n)
          ((commonFiniteApproximationSequence W original horiginal l).mark ∘ samples n)) atTop
          (𝓝 (markedDensity P W (fun i =>
            (commonFiniteApproximationSequence W original horiginal l).mark ⁻¹' {i}))) := by
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
  obtain ⟨samples,htests⟩ := exists_realization_of_finite_common_cut μ N hN G W hconv
    sizes marks hmarks
  exact ⟨samples,htests 0,fun l => htests (l+1)⟩

/-- Every positive measurable region is realized by induced finite graphs,
without any assumption that its complement has positive measure. -/
theorem exists_region_realization {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℕ} (c₀ : Fin r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (hconv : FiniteGraphCommonCutConverges μ N G W)
    (S : Set α) (hS : MeasurableSet S) (hSpos : 0 < μ.real S)
    [IsProbabilityMeasure (cond μ S)] :
    ∃ T : ∀ n, Finset (Fin (N n)),
      Tendsto (fun n => ((T n).card : ℝ) / (N n : ℝ)) atTop (𝓝 (μ.real S)) ∧
      Tendsto (fun n => (T n).card) atTop atTop ∧
      FiniteGraphCommonCutConverges (cond μ S) (fun n => (T n).card)
        (fun n c => selectedGraph (G n c) (T n)) (fun c => restrictGraphon (W c) S) := by
  obtain ⟨mark,hmark,_,hinner⟩ := exists_lifting_mark S hS
    (fun i : Fin 0 => isEmptyElim i) (fun i => isEmptyElim i)
    (fun i => isEmptyElim i) (fun i => isEmptyElim i)
  let J : Set (Fin 2) := {j | j.val ≤ 0}
  have hpre : mark ⁻¹' J = S := hinner
  obtain ⟨samples,hOriginal,hApprox⟩ := exists_marked_realization μ N hN G W hconv mark hmark
  let T := fun n => @Finset.filter (Fin (N n))
    (fun v => mark (samples n v) ∈ J) (fun _ => Classical.propDecidable _) Finset.univ
  have hmass := selected_mass_tendsto c₀ N G (fun n => mark ∘ samples n) W mark hmark J hOriginal
  have hmass' : Tendsto (fun n => ((T n).card : ℝ) / (N n : ℝ)) atTop (𝓝 (μ.real S)) := by
    have h := hmass
    rw [hpre] at h
    apply h.congr'
    filter_upwards [] with n
    congr 2
  have horder : Tendsto (fun n => (T n).card) atTop atTop := by
    have h := selected_order_tendsto_of_order_tendsto N hN
      (fun n => mark ∘ samples n) J (by rwa [hpre]) hmass
    apply h.congr'
    filter_upwards [] with n
    apply congrArg Finset.card
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, Function.comp_apply]
  refine ⟨T,hmass',horder, ?_⟩
  have hpos : 0 < μ.real (mark ⁻¹' J) := by rwa [hpre]
  letI : IsProbabilityMeasure (cond μ (mark ⁻¹' J)) := by rwa [hpre]
  have hcut := induced_common_cut_of_marked_patterns c₀ N hN G W mark hmark samples
    hOriginal hApprox J hpos
  have htransfer (R : Set α) (hR : R = mark ⁻¹' J)
      [IsProbabilityMeasure (cond μ R)] :
      FiniteGraphCommonCutConverges (cond μ R) (fun n => (T n).card)
        (fun n c => selectedGraph (G n c) (T n)) (fun c => restrictGraphon (W c) R) := by
    subst R
    unfold FiniteGraphCommonCutConverges
    dsimp only [T]
    exact hcut
  exact htransfer S hpre.symm

end HadwigerRamsey4Col.Realization
