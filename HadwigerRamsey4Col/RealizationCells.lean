import HadwigerRamsey4Col.Sampling
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Pi

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace HadwigerRamsey4Col.Realization

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- The normalized measure on one vertex cell. -/
noncomputable def cellConditionalMeasure {n : ℕ} (cell : α → Fin n) (v : Fin n) : Measure α :=
  ProbabilityTheory.cond μ (cell ⁻¹' {v})

lemma cellConditionalMeasure_probability {n : ℕ} (hn : 0 < n)
    (cell : α → Fin n) (hcellmass : ∀ v, μ.real (cell ⁻¹' {v}) = 1/(n : ℝ))
    (v : Fin n) : IsProbabilityMeasure (cellConditionalMeasure μ cell v) := by
  apply cond_isProbabilityMeasure
  intro hzero
  have h := hcellmass v
  rw [measureReal_def, hzero, ENNReal.toReal_zero] at h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < 1/(n : ℝ) := by positivity
  linarith

lemma cellConditionalMeasure_apply {n : ℕ} (cell : α → Fin n)
    (hcell : Measurable cell) (hcellmass : ∀ v, μ.real (cell ⁻¹' {v}) = 1/(n : ℝ))
    (v : Fin n) (A : Set α) :
    (cellConditionalMeasure μ cell v).real A = (n : ℝ) * μ.real ((cell ⁻¹' {v}) ∩ A) := by
  rw [measureReal_def, cellConditionalMeasure, cond_apply (hcell (measurableSet_singleton _)),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (μ.real (cell ⁻¹' {v}))⁻¹ * μ.real ((cell ⁻¹' {v}) ∩ A) = _
  rw [hcellmass, one_div, inv_inv]

lemma cellConditionalMeasure_support {n : ℕ} (cell : α → Fin n)
    (hcell : Measurable cell) (v : Fin n) :
    ∀ᵐ x ∂cellConditionalMeasure μ cell v, cell x = v :=
  ae_cond_mem (hcell (measurableSet_singleton _))

lemma cellConditionalMeasure_map_singleton {n : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (cell : α → Fin n) (hcell : Measurable cell)
    (hcellmass : ∀ v, μ.real (cell ⁻¹' {v}) = 1/(n : ℝ))
    (mark : α → K) (hmark : Measurable mark) (v : Fin n) (a : K) :
    ((cellConditionalMeasure μ cell v).map mark).real {a} =
      (n : ℝ) * μ.real ((cell ⁻¹' {v}) ∩ (mark ⁻¹' {a})) := by
  change ((cellConditionalMeasure μ cell v).map mark {a}).toReal = _
  rw [Measure.map_apply hmark (measurableSet_singleton a)]
  exact cellConditionalMeasure_apply μ cell hcell hcellmass v _

noncomputable def cellLabelProbability {n k : ℕ} (cell : α → Fin n)
    (part : α → Fin k) (v : Fin n) (i : Fin k) : ℝ :=
  (n : ℝ) * μ.real ((cell ⁻¹' {v}) ∩ (part ⁻¹' {i}))

lemma cellLabelProbability_nonneg {n k : ℕ} (cell : α → Fin n)
    (part : α → Fin k) (v : Fin n) (i : Fin k) :
    0 ≤ cellLabelProbability μ cell part v i := by
  unfold cellLabelProbability
  positivity

lemma cellLabelProbability_sum {n k : ℕ} (hn : 0 < n)
    (cell : α → Fin n) (hcell : Measurable cell)
    (hcellmass : ∀ v, μ.real (cell ⁻¹' {v}) = 1/(n : ℝ))
    (part : α → Fin k) (hpart : Measurable part) (v : Fin n) :
    ∑ i, cellLabelProbability μ cell part v i = 1 := by
  have hdis : Pairwise (fun i j : Fin k => Disjoint
      ((cell ⁻¹' {v}) ∩ (part ⁻¹' {i})) ((cell ⁻¹' {v}) ∩ (part ⁻¹' {j}))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij ((hi.2).symm.trans hj.2)
  have hmeas : ∀ i : Fin k, MeasurableSet ((cell ⁻¹' {v}) ∩ (part ⁻¹' {i})) :=
    fun i => (hcell (measurableSet_singleton _)).inter (hpart (measurableSet_singleton _))
  have hcov : (⋃ i : Fin k, (cell ⁻¹' {v}) ∩ (part ⁻¹' {i})) = cell ⁻¹' {v} := by
    ext x
    simp
  have hsum := measureReal_iUnion_fintype (μ := μ) hdis hmeas
  rw [hcov, hcellmass] at hsum
  simp only [cellLabelProbability, ← Finset.mul_sum]
  rw [← hsum]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Expand an integral of a finite-cell function into its exact finite sum.
The class sets may overlap and may have zero measure. -/
theorem integral_cell_expansion {I V : Type*} [Fintype I] [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (cell : α → V) (hcell : Measurable cell)
    (A : I → Set α) (hA : ∀ i, MeasurableSet (A i)) (f : (I → V) → ℝ) :
    (∫ x : I → α, (∏ i, (A i).indicator (fun _ => (1 : ℝ)) (x i)) *
      f (fun i => cell (x i)) ∂Measure.pi (fun _ => μ)) =
    ∑ φ : I → V, f φ * ∏ i, μ.real ((A i) ∩ (cell ⁻¹' {φ i})) := by
  have hpoint (x : I → α) :
      (∏ i, (A i).indicator (fun _ => (1 : ℝ)) (x i)) * f (fun i => cell (x i)) =
      ∑ φ : I → V, f φ * ∏ i,
        ((A i) ∩ (cell ⁻¹' {φ i})).indicator (fun _ => (1 : ℝ)) (x i) := by
    rw [Finset.sum_eq_single (fun i => cell (x i))]
    · rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : x i ∈ A i <;> simp [h]
    · intro φ hφ hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hzero : (∏ j, ((A j) ∩ (cell ⁻¹' {φ j})).indicator
          (fun _ => (1 : ℝ)) (x j)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        have hnot : x i ∉ (A i) ∩ (cell ⁻¹' {φ i}) := by
          intro h
          exact hi h.2.symm
        exact Set.indicator_of_notMem hnot _
      rw [hzero, mul_zero]
    · simp
  have hterm (φ : I → V) : Integrable (fun x : I → α =>
      f φ * ∏ i, ((A i) ∩ (cell ⁻¹' {φ i})).indicator
        (fun _ => (1 : ℝ)) (x i)) (Measure.pi (fun _ => μ)) := by
    apply Integrable.const_mul
    apply Integrable.of_mem_Icc 0 1
    · apply Finset.aemeasurable_fun_prod
      intro i hi
      exact (((measurable_const.indicator ((hA i).inter
        (hcell (measurableSet_singleton _))))).comp (measurable_pi_apply i)).aemeasurable
    · apply Eventually.of_forall
      intro x
      constructor
      · apply Finset.prod_nonneg
        intro i hi
        by_cases h : x i ∈ (A i) ∩ (cell ⁻¹' {φ i}) <;> simp [h]
      · apply Finset.prod_le_one
        · intro i hi
          by_cases h : x i ∈ (A i) ∩ (cell ⁻¹' {φ i}) <;> simp [h]
        · intro i hi
          by_cases h : x i ∈ (A i) ∩ (cell ⁻¹' {φ i}) <;> simp [h]
  simp_rw [hpoint]
  rw [integral_finset_sum _ (fun φ _ => hterm φ)]
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [integral_const_mul, integral_fintype_prod_eq_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [integral_indicator ((hA i).inter (hcell (measurableSet_singleton _))), setIntegral_const]
  simp [measureReal_def]

end HadwigerRamsey4Col.Realization
