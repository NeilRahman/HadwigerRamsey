import Mathlib

open scoped BigOperators NNReal
open Finset MeasureTheory ProbabilityTheory Real

namespace HadwigerRamsey.ThomasonUpper

/-- The finite probabilistic method: a union bound strictly below one
leaves an outcome avoiding every bad event. -/
theorem exists_avoiding_events {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (h : (∑ i, μ.real (A i)) < 1) : ∃ ω, ∀ i, ω ∉ A i := by
  classical
  by_contra hn
  push Not at hn
  have he : (⋃ i, A i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨i, hi⟩ := hn ω
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hh := measureReal_iUnion_fintype_le (μ := μ) A
  rw [he, probReal_univ] at hh
  linarith

/-- Count events by their real-valued indicators. -/
noncomputable def eventCount {I Ω : Type*} (A : I → Set Ω) (s : Finset I) (ω : Ω) : ℝ :=
  ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω

/-- Independent indicators, centered by their expectations, are sub-Gaussian. -/
theorem eventCount_subgaussian {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (s : Finset I) :
    HasSubgaussianMGF (fun ω => eventCount A s ω - ∑ i ∈ s, μ.real (A i))
      ((s.card : ℝ≥0)/4) μ := by
  classical
  let X := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hmeas : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  have hint : ∀ i, ∫ ω, X i ω ∂μ = μ.real (A i) := by
    intro i
    simp [X, hA i]
  have hsub : ∀ i, HasSubgaussianMGF (fun ω => X i ω - μ.real (A i)) (1/4 : ℝ≥0) μ := by
    intro i
    have hh := hasSubgaussianMGF_of_mem_Icc (hmeas i).aemeasurable
      (ae_of_all μ (fun ω => show X i ω ∈ Set.Icc (0:ℝ) 1 by
        by_cases h : ω ∈ A i <;> simp [X, h]))
    convert hh using 1 <;> norm_num [hint]
  have hi : iIndepFun X μ := hind.iIndepFun_indicator
  have hic : iIndepFun (fun i ω => X i ω - μ.real (A i)) μ :=
    hi.comp (fun i x => x - μ.real (A i)) (fun _ => measurable_id.sub_const _)
  have hh := HasSubgaussianMGF.sum_of_iIndepFun hic
    (c := fun _ => (1/4 : ℝ≥0)) (s := s) (fun i _ => hsub i)
  convert hh using 1
  · funext ω
    simp only [eventCount, X, sum_sub_distrib]
  · simp [div_eq_mul_inv]

/-- Hoeffding's upper bound for a finite independent family of events. -/
theorem eventCount_upper_tail {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (s : Finset I) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (∑ i ∈ s, μ.real (A i)) + t ≤ eventCount A s ω} ≤
      exp (-2*t^2/(s.card : ℝ)) := by
  have hh := (eventCount_subgaussian μ A hA hind s).measure_ge_le ht
  have he : {ω | t ≤ eventCount A s ω - ∑ i ∈ s, μ.real (A i)} =
      {ω | (∑ i ∈ s, μ.real (A i)) + t ≤ eventCount A s ω} := by
    ext ω
    change (t ≤ eventCount A s ω - ∑ i ∈ s, μ.real (A i)) ↔
      ((∑ i ∈ s, μ.real (A i)) + t ≤ eventCount A s ω)
    constructor <;> intro h <;> linarith
  rw [he] at hh
  convert hh using 1 <;> push_cast <;> congr 1 <;> ring

/-- Hoeffding's lower bound, with the same constant as the upper bound. -/
theorem eventCount_lower_tail {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (s : Finset I) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | eventCount A s ω + t ≤ ∑ i ∈ s, μ.real (A i)} ≤
      exp (-2*t^2/(s.card : ℝ)) := by
  have hh := (eventCount_subgaussian μ A hA hind s).neg.measure_ge_le ht
  have he : {ω | t ≤ -(eventCount A s ω - ∑ i ∈ s, μ.real (A i))} =
      {ω | eventCount A s ω + t ≤ ∑ i ∈ s, μ.real (A i)} := by
    ext ω
    change (t ≤ -(eventCount A s ω - ∑ i ∈ s, μ.real (A i))) ↔
      (eventCount A s ω + t ≤ ∑ i ∈ s, μ.real (A i))
    constructor <;> intro h <;> linarith
  change μ.real {ω | t ≤ -(eventCount A s ω - ∑ i ∈ s, μ.real (A i))} ≤ _ at hh
  rw [he] at hh
  convert hh using 1 <;> push_cast <;> congr 1 <;> ring

/-- A uniform lower bound on the individual event probabilities gives a
lower-tail bound without assuming identically distributed events. -/
theorem eventCount_below_half {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (s : Finset I) {q : ℝ} (hq : 0 ≤ q) (hp : ∀ i ∈ s, q ≤ μ.real (A i)) :
    μ.real {ω | eventCount A s ω ≤ q*s.card/2} ≤ exp (-q^2*s.card/2) := by
  have hm : q*(s.card : ℝ) ≤ ∑ i ∈ s, μ.real (A i) := by
    simpa [mul_comm] using (sum_le_sum hp : (∑ _i ∈ s, q) ≤ ∑ i ∈ s, μ.real (A i))
  have hh := eventCount_lower_tail μ A hA hind s
    (t := q*s.card/2) (by positivity)
  have hsub : {ω | eventCount A s ω ≤ q*s.card/2} ⊆
      {ω | eventCount A s ω + q*s.card/2 ≤ ∑ i ∈ s, μ.real (A i)} := by
    intro ω h
    change eventCount A s ω ≤ q*s.card/2 at h
    change eventCount A s ω + q*s.card/2 ≤ _
    linarith
  apply (measureReal_mono hsub).trans
  convert hh using 1
  congr 1
  by_cases hs : s.card = 0
  · simp [hs]
  · have hsR : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    field_simp

end HadwigerRamsey.ThomasonUpper
