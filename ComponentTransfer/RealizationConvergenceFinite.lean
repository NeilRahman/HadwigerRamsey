import ComponentTransfer.RealizationConvergenceC4
import ComponentTransfer.RealizationConvergenceCost
import Graphon.CutNormPullback
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory Set
open scoped BigOperators

namespace ComponentTransfer.Realization

/-- Uniform measure on a nonempty finite carrier. -/
noncomputable def uniformFiniteMeasure (V : Type*) [Fintype V] [Nonempty V]
    [MeasurableSpace V] : Measure V := (PMF.uniformOfFintype V).toMeasure

instance uniformFiniteMeasure_probability (V : Type*) [Fintype V] [Nonempty V]
    [MeasurableSpace V] : IsProbabilityMeasure (uniformFiniteMeasure V) := by
  unfold uniformFiniteMeasure
  infer_instance

/-- Empirical mass, defined also when the finite carrier is empty. -/
noncomputable def finiteMarkMass {V K : Type*} [Fintype V] [DecidableEq K]
    (mark : V → K) (i : K) : ℝ := 𝔼 v, if mark v = i then 1 else 0

variable {V : Type*} [Fintype V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  {ν : Measure V} [IsProbabilityMeasure ν]

lemma uniformFiniteMeasure_singleton (v : V) :
    (uniformFiniteMeasure V).real {v} = 1 / Fintype.card V := by
  rw [measureReal_def, uniformFiniteMeasure,
    PMF.toMeasure_apply_singleton _ v (measurableSet_singleton v), PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

omit [Nonempty V] in
lemma integral_uniform_eq_expect (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V)
    (f : V → ℝ) : (∫ x, f x ∂ν) = 𝔼 x, f x := by
  rw [integral_fintype Integrable.of_finite, Finset.expect_eq_sum_div_card]
  simp only [hmass, smul_eq_mul, Finset.card_univ]
  rw [← Finset.mul_sum]
  ring

lemma uniformFiniteMeasure_mark_mass {K : Type*} [DecidableEq K]
    (mark : V → K) (i : K) :
    (uniformFiniteMeasure V).real (mark ⁻¹' {i}) = finiteMarkMass mark i := by
  classical
  have hs : MeasurableSet (mark ⁻¹' {i}) := (Set.toFinite _).measurableSet
  have h := integral_uniform_eq_expect (ν := uniformFiniteMeasure V)
    uniformFiniteMeasure_singleton ((mark ⁻¹' {i}).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator hs, setIntegral_const] at h
  simpa [finiteMarkMass, Set.indicator_apply] using h

omit [Nonempty V] in
lemma setIntegral_uniform_eq_expect (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V)
    (f : V → ℝ) (S : Set V) :
    (∫ x in S, f x ∂ν) = 𝔼 x, S.indicator (fun _ => (1 : ℝ)) x * f x := by
  classical
  rw [← integral_indicator (Set.toFinite S).measurableSet,
    integral_uniform_eq_expect hmass]
  apply Finset.expect_congr rfl
  intro x _
  by_cases hx : x ∈ S <;> simp [hx]

lemma finite_rectIntegralDiff_eq (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V)
    (U W : Graphon V ν) (S T : Set V) :
    Graphon.rectIntegralDiff U W S T =
      finiteRectangle (fun x y => U.toAEEqFun (x, y) - W.toAEEqFun (x, y))
        (S.indicator (fun _ => 1)) (T.indicator (fun _ => 1)) := by
  rw [Graphon.rectIntegralDiff, setIntegral_prod _ Integrable.of_finite]
  simp_rw [setIntegral_uniform_eq_expect hmass]
  unfold finiteRectangle
  apply Finset.expect_congr rfl
  intro x _
  congr 1
  apply Finset.expect_congr rfl
  intro y _
  ring

/-- Four-cycle control gives cut-norm control for uniform finite graphons. -/
theorem finite_cutNormDiff_le_of_C4_le
    (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V)
    (U W : Graphon V ν) {ε : ℝ} (hε : 0 ≤ ε)
    (hC4 : finiteC4 (fun x y => U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ≤ ε ^ 4) :
    Graphon.cutNormDiff U W ≤ ε := by
  classical
  unfold Graphon.cutNormDiff
  apply Real.iSup_le _ hε
  intro S
  apply Real.iSup_le _ hε
  intro _
  apply Real.iSup_le _ hε
  intro T
  apply Real.iSup_le _ hε
  intro _
  rw [finite_rectIntegralDiff_eq hmass]
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hε
  rw [(by decide : Even 4).pow_abs]
  apply (finite_rectangle_pow_four_le_C4 _ _ _ ?_ ?_).trans hC4
  · intro x
    by_cases hx : x ∈ S <;> simp [hx]
  · intro x
    by_cases hx : x ∈ T <;> simp [hx]

omit [MeasurableSingletonClass V] [IsProbabilityMeasure ν] in
lemma uniform_prod_singleton_ne_zero
    (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V) (p : V × V) :
    (ν.prod ν) {p} ≠ 0 := by
  have hv (v : V) : ν {v} ≠ 0 := by
    intro hz
    have h := hmass v
    rw [measureReal_def, hz, ENNReal.toReal_zero] at h
    have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have : 0 < 1 / (Fintype.card V : ℝ) := by positivity
    linarith
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  exact mul_ne_zero (hv p.1) (hv p.2)

lemma markedGraphon_uniform_apply {K : Type*} [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V)
    (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1) (mark : V → K) (hmark : Measurable mark)
    (x y : V) :
    (markedGraphon (μ := ν) B hBsymm hB mark hmark).toAEEqFun (x, y) =
      B (mark x) (mark y) :=
  ae_iff_of_countable.mp (markedGraphon_ae B hBsymm hB mark hmark) (x, y)
    (uniform_prod_singleton_ne_zero hmass (x, y))

/-- The C4 estimate stated directly for the two finite matrices, without
exposing representatives of almost-everywhere function classes. -/
theorem matrix_cutNormDiff_le_of_C4_le {K : Type*} [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (hmass : ∀ v, ν.real {v} = 1 / Fintype.card V)
    (A : V → V → ℝ) (hAsymm : ∀ i j, A i j = A j i)
    (hA : ∀ i j, A i j ∈ Icc (0 : ℝ) 1)
    (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1)
    (mark : V → K) (hmark : Measurable mark) {ε : ℝ} (hε : 0 ≤ ε)
    (hC4 : finiteC4 (fun x y => A x y - B (mark x) (mark y)) ≤ ε ^ 4) :
    Graphon.cutNormDiff (markedGraphon (μ := ν) A hAsymm hA id measurable_id)
      (markedGraphon B hBsymm hB mark hmark) ≤ ε := by
  apply finite_cutNormDiff_le_of_C4_le hmass _ _ hε
  simpa only [markedGraphon_uniform_apply hmass, id_eq] using hC4

end ComponentTransfer.Realization
