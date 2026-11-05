import Graphon.CutNormPullback

open MeasureTheory Set Filter

namespace ComponentTransfer.Realization

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

lemma cutNormDiff_le_integral_abs (U W : Graphon α μ) :
    Graphon.cutNormDiff U W ≤ ∫ p, |U.toAEEqFun p - W.toAEEqFun p| ∂μ.prod μ := by
  have hn : 0 ≤ ∫ p, |U.toAEEqFun p - W.toAEEqFun p| ∂μ.prod μ :=
    integral_nonneg fun _ => abs_nonneg _
  unfold Graphon.cutNormDiff
  apply Real.iSup_le _ hn
  intro S
  apply Real.iSup_le _ hn
  intro _
  apply Real.iSup_le _ hn
  intro T
  apply Real.iSup_le _ hn
  intro _
  apply abs_integral_le_integral_abs.trans
  exact setIntegral_le_integral
    ((SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)).abs
    (Eventually.of_forall fun _ => abs_nonneg _)

/-- Kernels which differ only at pairs meeting an exceptional set have cut
distance at most twice the mass of that set. -/
theorem cutNormDiff_le_two_measure_bad (U W : Graphon α μ) (bad : Set α)
    (hbad : MeasurableSet bad)
    (heq : ∀ᵐ p ∂μ.prod μ, p.1 ∉ bad → p.2 ∉ bad → U.toAEEqFun p = W.toAEEqFun p) :
    Graphon.cutNormDiff U W ≤ 2 * μ.real bad := by
  let b : α → ℝ := bad.indicator (fun _ => 1)
  have hb : Measurable b := measurable_const.indicator hbad
  have hb01 (x : α) : b x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ bad <;> simp [b, hx]
  have hbf : Integrable (fun p : α × α => b p.1) (μ.prod μ) :=
    Integrable.of_mem_Icc 0 1 (hb.comp measurable_fst).aemeasurable
      (Eventually.of_forall fun p => hb01 p.1)
  have hbs : Integrable (fun p : α × α => b p.2) (μ.prod μ) :=
    Integrable.of_mem_Icc 0 1 (hb.comp measurable_snd).aemeasurable
      (Eventually.of_forall fun p => hb01 p.2)
  calc
    Graphon.cutNormDiff U W ≤ ∫ p, |U.toAEEqFun p - W.toAEEqFun p| ∂μ.prod μ :=
      cutNormDiff_le_integral_abs U W
    _ ≤ ∫ p, b p.1 + b p.2 ∂μ.prod μ := by
      apply integral_mono_ae
        ((SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)).abs
        (hbf.add hbs)
      filter_upwards [U.ae_mem_Icc, W.ae_mem_Icc, heq] with p hU hW heq
      change |U.toAEEqFun p - W.toAEEqFun p| ≤ b p.1 + b p.2
      by_cases h₁ : p.1 ∈ bad <;> by_cases h₂ : p.2 ∈ bad
      · simp only [b, indicator_of_mem h₁, indicator_of_mem h₂]
        rw [abs_le]
        constructor <;> linarith [hU.1, hU.2, hW.1, hW.2]
      · simp only [b, indicator_of_mem h₁, indicator_of_notMem h₂, add_zero]
        rw [abs_le]
        constructor <;> linarith [hU.1, hU.2, hW.1, hW.2]
      · simp only [b, indicator_of_notMem h₁, indicator_of_mem h₂, zero_add]
        rw [abs_le]
        constructor <;> linarith [hU.1, hU.2, hW.1, hW.2]
      · simp [b, h₁, h₂, heq h₁ h₂]
    _ = 2 * μ.real bad := by
      rw [integral_add hbf hbs, integral_fun_fst, integral_fun_snd]
      simp [b, integral_indicator hbad, two_mul]

section Marked

variable {K : Type*} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

/-- A bounded symmetric matrix pulled back along a measurable finite marking. -/
noncomputable def markedGraphon (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1) (mark : α → K) (hmark : Measurable mark) :
    Graphon α μ := by
  let f : α × α → ℝ := fun p => B (mark p.1) (mark p.2)
  have hf : AEStronglyMeasurable f (μ.prod μ) :=
    ((Measurable.of_discrete : Measurable (fun q : K × K => B q.1 q.2)).comp
      ((hmark.comp measurable_fst).prodMk (hmark.comp measurable_snd))).aestronglyMeasurable
  refine ⟨⟨AEEqFun.mk f hf, ?_⟩, ?_⟩
  · filter_upwards [AEEqFun.coeFn_mk f hf, ae_prod_swap (AEEqFun.coeFn_mk f hf)] with p hp hs
    rw [hp, hs]
    exact hBsymm _ _
  · filter_upwards [AEEqFun.coeFn_mk f hf] with p hp
    rw [hp]
    exact hB _ _

lemma markedGraphon_ae (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1) (mark : α → K) (hmark : Measurable mark) :
    ∀ᵐ p ∂μ.prod μ,
      (markedGraphon (μ := μ) B hBsymm hB mark hmark).toAEEqFun p =
        B (mark p.1) (mark p.2) :=
  AEEqFun.coeFn_mk _ _

lemma markedGraphon_pullback {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [IsProbabilityMeasure ν] (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1) (mark : β → K) (hmark : Measurable mark)
    (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    Graphon.pullback (markedGraphon (μ := ν) B hBsymm hB mark hmark) φ hφ =
      markedGraphon B hBsymm hB (mark ∘ φ) (hmark.comp hφ.measurable) := by
  apply Graphon.ext
  apply SymmKernel.ext
  apply AEEqFun.ext
  have hraw := (hφ.prod hφ).quasiMeasurePreserving.ae
    (markedGraphon_ae (μ := ν) B hBsymm hB mark hmark)
  filter_upwards [Graphon.pullback_ae (markedGraphon (μ := ν) B hBsymm hB mark hmark) φ hφ,
    markedGraphon_ae (μ := μ) B hBsymm hB (mark ∘ φ) (hmark.comp hφ.measurable),
    hraw] with p hp hq hr
  exact hp.trans (hr.trans hq.symm)

/-- One alignment controls every matrix supported on the same finite marking. -/
theorem markedGraphon_cutNormDiff_le (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1)
    (mark₁ mark₂ : α → K) (hm₁ : Measurable mark₁) (hm₂ : Measurable mark₂) :
    Graphon.cutNormDiff (markedGraphon (μ := μ) B hBsymm hB mark₁ hm₁)
        (markedGraphon (μ := μ) B hBsymm hB mark₂ hm₂) ≤
      2 * μ.real {x | mark₁ x ≠ mark₂ x} := by
  apply cutNormDiff_le_two_measure_bad _ _ _ (measurableSet_eq_fun hm₁ hm₂).compl
  filter_upwards [markedGraphon_ae B hBsymm hB mark₁ hm₁,
    markedGraphon_ae B hBsymm hB mark₂ hm₂] with p hp₁ hp₂ h₁ h₂
  change ¬ mark₁ p.1 ≠ mark₂ p.1 at h₁
  change ¬ mark₁ p.2 ≠ mark₂ p.2 at h₂
  rw [hp₁, hp₂, not_not.mp h₁, not_not.mp h₂]

/-- Cut cost under a common coupling is controlled by the two approximation
errors and by the probability that the finite markings fail to match. -/
theorem coupling_cost_le {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure β} {ρ : Measure γ} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (U : Graphon β ν) (W : Graphon γ ρ)
    (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1)
    (mark₁ : β → K) (mark₂ : γ → K) (hm₁ : Measurable mark₁) (hm₂ : Measurable mark₂)
    (φ : α → β) (ψ : α → γ) (hφ : MeasurePreserving φ μ ν)
    (hψ : MeasurePreserving ψ μ ρ) :
    Graphon.cutNormDiff (Graphon.pullback U φ hφ) (Graphon.pullback W ψ hψ) ≤
      Graphon.cutNormDiff U (markedGraphon B hBsymm hB mark₁ hm₁) +
      Graphon.cutNormDiff W (markedGraphon B hBsymm hB mark₂ hm₂) +
      2 * μ.real {x | mark₁ (φ x) ≠ mark₂ (ψ x)} := by
  have h := Graphon.abs_cutNormDiff_pullback_sub_le U
    (markedGraphon B hBsymm hB mark₁ hm₁) W
    (markedGraphon B hBsymm hB mark₂ hm₂) φ ψ hφ hψ
  rw [markedGraphon_pullback, markedGraphon_pullback] at h
  have hb := markedGraphon_cutNormDiff_le (μ := μ) B hBsymm hB
    (mark₁ ∘ φ) (mark₂ ∘ ψ) (hm₁.comp hφ.measurable) (hm₂.comp hψ.measurable)
  have hh := (abs_le.mp h).2
  dsimp only [Function.comp_apply] at hb
  linarith

end Marked

end ComponentTransfer.Realization
