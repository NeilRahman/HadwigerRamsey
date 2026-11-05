import HadwigerRamsey4Col.LiftingExpansionCompact
import HadwigerRamsey4Col.RealizationCommonApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence

open scoped Topology Classical BigOperators
open MeasureTheory Filter Set

namespace HadwigerRamsey4Col.Lifting

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def clippedDensity (φ : CutDual μ) (x : α) : ℝ :=
  max 0 (min 1 (dualDensity μ φ x))

lemma clippedDensity_measurable (φ : CutDual μ) : Measurable (clippedDensity μ φ) :=
  measurable_const.max (measurable_const.min (Lp.stronglyMeasurable (dualDensity μ φ)).measurable)

lemma clippedDensity_bounds (φ : CutDual μ) (x : α) : clippedDensity μ φ x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

lemma clippedDensity_eq {ρ : ℝ} {φ : CutDual μ} (hφ : φ ∈ fractionalCuts μ ρ) :
    clippedDensity μ φ =ᵐ[μ] dualDensity μ φ := by
  filter_upwards [fractionalCuts_density_bounds μ hφ] with x hx
  exact max_eq_right (le_min zero_le_one hx.1) |>.trans (min_eq_right hx.2)

lemma clippedDensity_setIntegral {ρ : ℝ} {φ : CutDual μ} (hφ : φ ∈ fractionalCuts μ ρ)
    (A : Set α) (hA : MeasurableSet A) :
    ∫ x in A, clippedDensity μ φ x ∂μ = φ (cutIndicator μ A hA) := by
  rw [integral_congr_ae (ae_restrict_of_ae (clippedDensity_eq μ hφ))]
  exact dualDensity_setIntegral μ φ A hA

lemma integral_finite_mark {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (mark : α → K) (hm : Measurable mark)
    (g : α → ℝ) (hg : Integrable g μ) (b : K → ℝ) :
    (∫ x, g x * b (mark x) ∂μ) = ∑ i, b i * ∫ x in mark ⁻¹' {i}, g x ∂μ := by
  have heq (x : α) : g x * b (mark x) =
      ∑ i : K, b i * (mark ⁻¹' {i}).indicator g x := by
    simp [Set.indicator_apply, mul_comm]
  simp_rw [heq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, integral_indicator (hm (measurableSet_singleton i))]
  · intro i hi
    exact (hg.indicator (hm (measurableSet_singleton i))).const_mul _

lemma integrable_finite_mark {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (mark : α → K) (hm : Measurable mark)
    (g : α → ℝ) (hg : Integrable g μ) (b : K → ℝ) :
    Integrable (fun x => g x * b (mark x)) μ := by
  have hh : Integrable (fun x => ∑ i : K, b i * (mark ⁻¹' {i}).indicator g x) μ :=
    integrable_finsetSum _ (fun i _ => (hg.indicator (hm (measurableSet_singleton i))).const_mul _)
  convert hh using 1
  funext x
  simp [Set.indicator_apply, mul_comm]

noncomputable def fractionalBoundary (W : Graphon α μ) (f : α → ℝ) : ℝ :=
  ∫ p, f p.1 * (1-f p.2) * W.toAEEqFun p ∂μ.prod μ

lemma fractionalBoundary_integrable (W : Graphon α μ) (f : α → ℝ)
    (hf : Measurable f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p : α × α => f p.1 * (1-f p.2) * W.toAEEqFun p) (μ.prod μ) := by
  apply (SymmKernel.graphon_integrable W).bdd_mul (c := 1)
  · exact ((hf.comp measurable_fst).mul (measurable_const.sub (hf.comp measurable_snd))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb p.1).1 (by linarith [(hb p.2).2]))]
    nlinarith [(hb p.1).1,(hb p.1).2,(hb p.2).1,(hb p.2).2]

lemma fractionalBoundary_cutNormDiff (U W : Graphon α μ) (f : α → ℝ)
    (hf : Measurable f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    |fractionalBoundary μ U f - fractionalBoundary μ W f| ≤ Graphon.cutNormDiff U W := by
  unfold fractionalBoundary
  rw [← integral_sub (fractionalBoundary_integrable μ U f hf hb)
    (fractionalBoundary_integrable μ W f hf hb)]
  simp_rw [← mul_sub]
  have hint : Integrable (fun p : α × α => f p.1 * (1-f p.2) *
      (U.toAEEqFun p-W.toAEEqFun p)) (μ.prod μ) := by
    convert (fractionalBoundary_integrable μ U f hf hb).sub
      (fractionalBoundary_integrable μ W f hf hb) using 1
    funext p
    simp only [Pi.sub_apply]
    ring
  rw [integral_prod _ hint]
  exact Graphon.abs_weighted_integral_diff_le U W f (fun x => 1-f x)
    hf (measurable_const.sub hf) hb (fun x => ⟨by linarith [(hb x).2],by linarith [(hb x).1]⟩)

lemma fractionalBoundary_marked {k : ℕ} (B : Fin k → Fin k → ℝ)
    (hBsymm : ∀ i j, B i j = B j i) (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1)
    (mark : α → Fin k) (hm : Measurable mark)
    (f : α → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    fractionalBoundary μ (Realization.markedGraphon B hBsymm hB mark hm) f =
      ∑ j : Fin k, (∫ x in mark ⁻¹' {j}, 1-f x ∂μ) *
        (∑ i : Fin k, B i j * ∫ x in mark ⁻¹' {i}, f x ∂μ) := by
  let Q := Realization.markedGraphon (μ := μ) B hBsymm hB mark hm
  have heq : (fun p : α × α => f p.1 * (1-f p.2) * Q.toAEEqFun p) =ᵐ[μ.prod μ]
      (fun p => f p.1 * (1-f p.2) * B (mark p.1) (mark p.2)) := by
    filter_upwards [Realization.markedGraphon_ae B hBsymm hB mark hm] with p hp
    rw [hp]
  have hi := (fractionalBoundary_integrable μ Q f hf hb).congr heq
  unfold fractionalBoundary
  rw [integral_congr_ae heq, integral_prod _ hi]
  have hfint : Integrable f μ := Integrable.of_mem_Icc 0 1 hf.aemeasurable (Eventually.of_forall hb)
  have hgint : Integrable (fun x => 1-f x) μ := (integrable_const 1).sub hfint
  have inner (x : α) :
      (∫ y, f x * (1-f y) * B (mark x) (mark y) ∂μ) =
      f x * ∑ j : Fin k, B (mark x) j * ∫ y in mark ⁻¹' {j}, 1-f y ∂μ := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_finite_mark μ mark hm _ hgint]
  simp_rw [inner, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    simp_rw [← mul_assoc]
    rw [integral_mul_const, integral_finite_mark μ mark hm f hfint (fun i => B i j), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro j hj
    have h := integrable_finite_mark μ mark hm f hfint (fun i => B i j)
    convert h.mul_const (∫ y in mark ⁻¹' {j}, 1-f y ∂μ) using 1
    funext x
    ring

noncomputable def stepBoundaryPolynomial {k : ℕ} (B : Fin k → Fin k → ℝ)
    (mark : α → Fin k) (hm : Measurable mark) (φ : CutDual μ) : ℝ :=
  ∑ j : Fin k, (μ.real (mark ⁻¹' {j}) - φ (cutIndicator μ (mark ⁻¹' {j}) (hm (measurableSet_singleton j)))) *
    (∑ i : Fin k, B i j * φ (cutIndicator μ (mark ⁻¹' {i}) (hm (measurableSet_singleton i))))

lemma stepBoundaryPolynomial_continuous {k : ℕ} (B : Fin k → Fin k → ℝ)
    (mark : α → Fin k) (hm : Measurable mark) :
    Continuous (stepBoundaryPolynomial μ B mark hm) := by
  apply continuous_finsetSum
  intro j hj
  apply Continuous.mul
  · exact continuous_const.sub (WeakDual.eval_continuous _)
  · apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul (WeakDual.eval_continuous _)

lemma stepBoundaryPolynomial_eq {k : ℕ} (B : Fin k → Fin k → ℝ)
    (hBsymm : ∀ i j, B i j = B j i) (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1)
    (mark : α → Fin k) (hm : Measurable mark) {ρ : ℝ} {φ : CutDual μ}
    (hφ : φ ∈ fractionalCuts μ ρ) :
    stepBoundaryPolynomial μ B mark hm φ =
      fractionalBoundary μ (Realization.markedGraphon B hBsymm hB mark hm) (clippedDensity μ φ) := by
  rw [fractionalBoundary_marked μ B hBsymm hB mark hm _
    (clippedDensity_measurable μ φ) (clippedDensity_bounds μ φ)]
  unfold stepBoundaryPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_sub (integrable_const 1).integrableOn
    (Integrable.of_mem_Icc 0 1 (clippedDensity_measurable μ φ).aemeasurable
      (Eventually.of_forall (clippedDensity_bounds μ φ))).integrableOn]
  have heval (i : Fin k) := clippedDensity_setIntegral μ hφ
    (mark ⁻¹' {i}) (hm (measurableSet_singleton i))
  simp_rw [heval]
  simp

end HadwigerRamsey4Col.Lifting
