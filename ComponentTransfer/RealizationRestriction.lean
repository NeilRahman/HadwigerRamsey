import ComponentTransfer.RealizationDefinitions
import ComponentTransfer.RealizationConvergenceCost
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Pi

open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory Filter Set Finset

namespace ComponentTransfer.Realization

/-- Conditioning every coordinate on a set is restriction of the product
measure, with precisely the expected normalization. -/
theorem pi_cond_eq {α V : Type*} [MeasurableSpace α] [Fintype V]
    (μ : Measure α) [IsProbabilityMeasure μ] (A : Set α)
    (hA : MeasurableSet A) (hpos : μ A ≠ 0) :
    Measure.pi (fun _ : V => cond μ A) =
      ((μ A)⁻¹ ^ Fintype.card V) •
        (Measure.pi (fun _ : V => μ)).restrict (Set.univ.pi (fun _ => A)) := by
  letI : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure hpos
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, Measure.pi_pi]
  simp_rw [cond_apply hA, Set.inter_comm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rfl

/-- Product of indicators is the indicator of the product set. -/
lemma prod_indicator_mul {α V : Type*} [Fintype V]
    (A : V → Set α) (f : (V → α) → ℝ) (x : V → α) :
    (∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v)) * f x =
      (Set.univ.pi A).indicator f x := by
  by_cases hx : ∀ v, x v ∈ A v
  · have hm : x ∈ Set.univ.pi A := by simp [Set.mem_pi, hx]
    rw [Set.indicator_of_mem hm]
    have hp : ∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v) = 1 :=
      Finset.prod_eq_one (fun v _ => Set.indicator_of_mem (hx v) _)
    rw [hp, one_mul]
  · have hm : x ∉ Set.univ.pi A := by simpa [Set.mem_pi] using hx
    rw [Set.indicator_of_notMem hm]
    push Not at hx
    obtain ⟨v, hv⟩ := hx
    have hp : ∏ v, (A v).indicator (fun _ => (1 : ℝ)) (x v) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)
    rw [hp, zero_mul]

/-- Restriction to a positive-measure set divides an m-vertex density by
its mass to the m-th power. This uses the actual normalized restricted measure. -/
theorem integral_pi_cond {α V : Type*} [MeasurableSpace α] [Fintype V]
    (μ : Measure α) [IsProbabilityMeasure μ] (A : Set α)
    (hA : MeasurableSet A) (hpos : μ A ≠ 0) (f : (V → α) → ℝ) :
    (∫ x : V → α, f x ∂Measure.pi (fun _ => cond μ A)) =
      (∫ x : V → α, (∏ v, A.indicator (fun _ => (1 : ℝ)) (x v)) * f x
        ∂Measure.pi (fun _ => μ)) / (μ.real A)^Fintype.card V := by
  rw [pi_cond_eq μ A hA hpos, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, smul_eq_mul]
  simp_rw [prod_indicator_mul]
  rw [integral_indicator (MeasurableSet.univ_pi (fun _ => hA))]
  change (μ.real A)⁻¹ ^ Fintype.card V * _ = _
  rw [inv_pow, div_eq_mul_inv, mul_comm]

section RestrictGraphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Restriction changes the probability measure and keeps the same kernel. -/
noncomputable def restrictGraphon (W : Graphon α μ) (A : Set α) :
    Graphon α (cond μ A) := by
  let hf : AEStronglyMeasurable W.toAEEqFun ((cond μ A).prod (cond μ A)) :=
    W.toAEEqFun.stronglyMeasurable.aestronglyMeasurable
  have hac : (cond μ A).prod (cond μ A) ≪ μ.prod μ :=
    cond_absolutelyContinuous.prod cond_absolutelyContinuous
  refine ⟨⟨AEEqFun.mk W.toAEEqFun hf, ?_⟩, ?_⟩
  · have hs := hac.ae_le W.symm'
    have h := AEEqFun.coeFn_mk W.toAEEqFun hf
    filter_upwards [h, ae_prod_swap h, hs] with p hp hswap hsym
    rw [hp, hswap]
    exact hsym
  · have hb := hac.ae_le W.ae_mem_Icc
    filter_upwards [AEEqFun.coeFn_mk W.toAEEqFun hf, hb] with p hp hbounds
    rw [hp]
    exact hbounds

theorem restrictGraphon_ae (W : Graphon α μ) (A : Set α) :
    ∀ᵐ p ∂(cond μ A).prod (cond μ A),
      (restrictGraphon W A).toAEEqFun p = W.toAEEqFun p :=
  AEEqFun.coeFn_mk _ _

theorem prod_cond_eq (A : Set α) :
    (cond μ A).prod (cond μ A) =
      ((μ A)⁻¹ ^ 2) • (μ.prod μ).restrict (A ×ˢ A) := by
  simp only [ProbabilityTheory.cond, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, pow_two, Measure.prod_restrict]

theorem restrictGraphon_rectIntegralDiff (U W : Graphon α μ) (A : Set α)
    (S T : Set α) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Graphon.rectIntegralDiff (restrictGraphon U A) (restrictGraphon W A) S T =
      Graphon.rectIntegralDiff U W (S ∩ A) (T ∩ A) / (μ.real A)^2 := by
  unfold Graphon.rectIntegralDiff
  have heq : (fun p => (restrictGraphon U A).toAEEqFun p -
      (restrictGraphon W A).toAEEqFun p) =ᵐ[(cond μ A).prod (cond μ A)]
      (fun p => U.toAEEqFun p - W.toAEEqFun p) := by
    filter_upwards [restrictGraphon_ae U A, restrictGraphon_ae W A] with p hp hq
    rw [hp, hq]
  rw [integral_congr_ae (ae_restrict_of_ae heq)]
  rw [prod_cond_eq, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict (hS.prod hT), Set.prod_inter_prod]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, smul_eq_mul]
  change (μ.real A)⁻¹ ^ 2 * _ = _
  rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- The normalization cost for restricting both graphon variables is the
square of the mass of the selected set. -/
theorem restrictGraphon_cutNormDiff_le (U W : Graphon α μ) (A : Set α)
    (hA : MeasurableSet A) [IsProbabilityMeasure (cond μ A)] :
    Graphon.cutNormDiff (restrictGraphon U A) (restrictGraphon W A) ≤
      Graphon.cutNormDiff U W / (μ.real A)^2 := by
  have hn : 0 ≤ Graphon.cutNormDiff U W / (μ.real A)^2 :=
    div_nonneg (Graphon.cutNormDiff_nonneg U W) (sq_nonneg _)
  unfold Graphon.cutNormDiff
  apply Real.iSup_le _ hn
  intro S
  apply Real.iSup_le _ hn
  intro hS
  apply Real.iSup_le _ hn
  intro T
  apply Real.iSup_le _ hn
  intro hT
  rw [restrictGraphon_rectIntegralDiff U W A S T hS hT, abs_div,
    abs_of_nonneg (sq_nonneg (μ.real A))]
  exact div_le_div_of_nonneg_right
    (Graphon.abs_rectIntegralDiff_le U W (hS.inter hA) (hT.inter hA)) (sq_nonneg _)

theorem restrictGraphon_cutNormDiff_tendsto (U : ℕ → Graphon α μ) (W : Graphon α μ)
    (A : Set α) (hA : MeasurableSet A) [IsProbabilityMeasure (cond μ A)]
    (hcut : Tendsto (fun n => Graphon.cutNormDiff (U n) W) atTop (nhds 0)) :
    Tendsto (fun n => Graphon.cutNormDiff (restrictGraphon (U n) A) (restrictGraphon W A))
      atTop (nhds 0) := by
  apply squeeze_zero (fun n => Graphon.cutNormDiff_nonneg _ _)
    (fun n => restrictGraphon_cutNormDiff_le (U n) W A hA)
  simpa using hcut.div_const ((μ.real A)^2)

/-- Restricting a finite marked kernel preserves its matrix and marking. -/
theorem restrictGraphon_markedGraphon {K : Type*} [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (B : K → K → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1)
    (mark : α → K) (hmark : Measurable mark) (A : Set α)
    [IsProbabilityMeasure (cond μ A)] :
    restrictGraphon (markedGraphon (μ := μ) B hBsymm hB mark hmark) A =
      markedGraphon (μ := cond μ A) B hBsymm hB mark hmark := by
  apply Graphon.ext
  apply SymmKernel.ext
  apply AEEqFun.ext
  have hac : (cond μ A).prod (cond μ A) ≪ μ.prod μ :=
    cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hsource := hac.ae_le (markedGraphon_ae (μ := μ) B hBsymm hB mark hmark)
  filter_upwards [restrictGraphon_ae (markedGraphon (μ := μ) B hBsymm hB mark hmark) A,
    hsource, markedGraphon_ae (μ := cond μ A) B hBsymm hB mark hmark] with p hr hs ht
  rw [hr, hs, ht]

/-- Marked test densities on the normalized restriction are precisely the
original densities with every vertex constrained to the selected set. -/
theorem restrictGraphon_markedDensity {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (B : Fin k → Set α) :
    markedDensity P (fun c => restrictGraphon (W c) A) B =
      markedDensity P W (fun i => A ∩ B i) / (μ.real A)^P.1 := by
  letI : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure hpos
  have he : ∀ e ∈ P.graph.edgeFinset,
      ∀ᵐ x : Fin P.1 → α ∂Measure.pi (fun _ => cond μ A),
      (restrictGraphon (W (P.colour e)) A).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2) =
      (W (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
    intro e he
    exact (pair_measurePreserving (μ := cond μ A) (Quot.out e).1 (Quot.out e).2
      (Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))).quasiMeasurePreserving.ae
      (restrictGraphon_ae (W (P.colour e)) A)
  have hall : ∀ᵐ x : Fin P.1 → α ∂Measure.pi (fun _ => cond μ A),
      ∀ e ∈ P.graph.edgeFinset,
      (restrictGraphon (W (P.colour e)) A).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2) =
      (W (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
    simpa only [ae_all_iff] using he
  unfold markedDensity
  calc
    _ = ∫ x : Fin P.1 → α,
        (∏ u, (B (P.label u)).indicator (fun _ => (1 : ℝ)) (x u)) *
          ∏ e ∈ P.graph.edgeFinset,
            (W (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
          ∂Measure.pi (fun _ => cond μ A) := by
      apply integral_congr_ae
      filter_upwards [hall] with x hx
      congr 1
      exact Finset.prod_congr rfl hx
    _ = _ := by
      rw [integral_pi_cond μ A hA hpos]
      simp only [Fintype.card_fin]
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      by_cases hxu : x u ∈ A <;> by_cases hxb : x u ∈ B (P.label u) <;>
        simp [hxu, hxb]

end RestrictGraphon

end ComponentTransfer.Realization
