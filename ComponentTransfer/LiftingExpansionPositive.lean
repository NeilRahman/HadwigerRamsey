import ComponentTransfer.RealizationConvergenceCost

open scoped Classical Topology
open MeasureTheory Filter Set

namespace ComponentTransfer.Lifting

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Connectedness in the graphon sense, using the standard positive-cut
characterization. -/
def Connected (W : Graphon α μ) : Prop :=
  ∀ A : Set α, MeasurableSet A → 0 < μ.real A → μ.real A < 1 →
    0 < W.toSymmKernel.rectIntegral A Aᶜ

noncomputable def fractionalCut (W : Graphon α μ) (f : α → ℝ) : ℝ :=
  ∫ p, W.toAEEqFun p * f p.1 * (1-f p.2) ∂μ.prod μ

lemma fractionalCut_integrable (W : Graphon α μ) (f : α → ℝ) (hf : Measurable f)
    (hbound : ∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => W.toAEEqFun p * f p.1 * (1-f p.2)) (μ.prod μ) := by
  apply Integrable.of_mem_Icc 0 1
  · exact ((W.toAEEqFun.aemeasurable.mul (hf.comp measurable_fst).aemeasurable).mul
      (measurable_const.sub (hf.comp measurable_snd)).aemeasurable)
  · filter_upwards [W.ae_mem_Icc,
      (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hbound,
      (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hbound] with p hW hx hy
    constructor
    · exact mul_nonneg (mul_nonneg hW.1 hx.1) (by linarith [hy.2])
    · have h₁ := mul_le_mul hW.2 hx.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1)
      have h₂ := mul_le_mul h₁ (show 1-f p.2 ≤ 1 by linarith [hy.1])
        (show 0 ≤ 1-f p.2 by linarith [hy.2]) (by norm_num : (0 : ℝ) ≤ 1*1)
      norm_num at h₂
      exact h₂

lemma fractionalCut_eq_of_ae_const (W : Graphon α μ) (f : α → ℝ) {m : ℝ}
    (heq : f =ᵐ[μ] fun _ => m) :
    fractionalCut W f = m*(1-m)*(∫ p, W.toAEEqFun p ∂μ.prod μ) := by
  unfold fractionalCut
  calc
    _ = ∫ p, (m*(1-m))*W.toAEEqFun p ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [
        (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae heq,
        (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae heq] with p hx hy
      rw [hx,hy]
      ring
    _ = _ := integral_const_mul _ _

/-- A nontrivial fractional cut of a connected graphon has positive weight.
The total-mass assumption excludes the vacuous zero kernel on an indivisible
atom; it follows automatically from connectedness on an atomless space. -/
theorem fractionalCut_pos (W : Graphon α μ) (hW : Connected W)
    (htotal : 0 < ∫ p, W.toAEEqFun p ∂μ.prod μ)
    (f : α → ℝ) (hf : Measurable f)
    (hbound : ∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1)
    (hm0 : 0 < ∫ x, f x ∂μ) (hm1 : (∫ x, f x ∂μ) < 1) :
    0 < fractionalCut W f := by
  let m := ∫ x, f x ∂μ
  let A : Set α := {x | m < f x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hfi : Integrable f μ := Integrable.of_mem_Icc 0 1 hf.aemeasurable hbound
  have hconst (heq : f =ᵐ[μ] fun _ => m) : 0 < fractionalCut W f := by
    rw [fractionalCut_eq_of_ae_const W f heq]
    exact mul_pos (mul_pos hm0 (sub_pos.mpr hm1)) htotal
  have hA0 : 0 ≤ μ.real A := ENNReal.toReal_nonneg
  have hA1 : μ.real A ≤ 1 := measureReal_le_one
  by_cases hzero : μ.real A = 0
  · have hz : μ A = 0 := (measureReal_eq_zero_iff (μ := μ)).mp hzero
    have hevent : ∀ᵐ x ∂μ, x ∉ A := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hz
    have hle : f ≤ᵐ[μ] fun _ => m := hevent.mono (fun x hx => le_of_not_gt hx)
    apply hconst
    apply (integral_eq_iff_of_ae_le hfi (integrable_const m) hle).mp
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  by_cases hone : μ.real A = 1
  · have hz : μ Aᶜ = 0 := by
      apply (measureReal_eq_zero_iff (μ := μ)).mp
      rw [probReal_compl_eq_one_sub hA, hone]
      ring
    have hevent : ∀ᵐ x ∂μ, x ∈ A := by
      rw [ae_iff]
      exact hz
    have hle : (fun _ => m) ≤ᵐ[μ] f := hevent.mono (fun x hx => le_of_lt hx)
    apply hconst
    apply EventuallyEq.symm
    apply (integral_eq_iff_of_ae_le (integrable_const m) hfi hle).mp
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  have hcut : 0 < W.toSymmKernel.rectIntegral A Aᶜ := hW A hA
    (lt_of_le_of_ne hA0 (Ne.symm hzero)) (lt_of_le_of_ne hA1 hone)
  have hrectmeas : MeasurableSet (A ×ˢ Aᶜ) := hA.prod hA.compl
  have hrectint : Integrable ((A ×ˢ Aᶜ).indicator W.toAEEqFun) (μ.prod μ) :=
    (SymmKernel.graphon_integrable W).indicator hrectmeas
  have hle : m*(1-m)*W.toSymmKernel.rectIntegral A Aᶜ ≤ fractionalCut W f := by
    calc
      _ = ∫ p, m*(1-m)*(A ×ˢ Aᶜ).indicator W.toAEEqFun p ∂μ.prod μ := by
        rw [integral_const_mul, integral_indicator hrectmeas]
        rfl
      _ ≤ _ := by
        apply integral_mono_ae (hrectint.const_mul _) (fractionalCut_integrable W f hf hbound)
        filter_upwards [W.ae_mem_Icc,
          (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hbound,
          (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hbound] with p hWp hx hy
        by_cases hp : p ∈ A ×ˢ Aᶜ
        · rw [Set.indicator_of_mem hp]
          have hfx : m ≤ f p.1 := (mem_prod.mp hp).1.le
          have hfy : f p.2 ≤ m := le_of_not_gt (mem_prod.mp hp).2
          have hprod := mul_le_mul hfx (sub_le_sub_left hfy 1)
            (sub_nonneg.mpr hm1.le) hx.1
          have hh := mul_le_mul_of_nonneg_left hprod hWp.1
          nlinarith only [hh]
        · rw [Set.indicator_of_notMem hp, mul_zero]
          exact mul_nonneg (mul_nonneg hWp.1 hx.1) (sub_nonneg.mpr hy.2)
  exact (mul_pos (mul_pos hm0 (sub_pos.mpr hm1)) hcut).trans_le hle

end ComponentTransfer.Lifting
