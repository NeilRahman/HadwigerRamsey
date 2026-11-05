import ComponentTransfer.LiftingExpansionBoundary
import ComponentTransfer.LiftingExpansionPositive
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.Compact

open scoped Topology BigOperators Classical
open MeasureTheory Filter Set

namespace ComponentTransfer.Lifting

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def dualBoundary (W : Graphon α μ) (φ : CutDual μ) : ℝ :=
  fractionalBoundary μ W (clippedDensity μ φ)

lemma dualBoundary_continuousOn (W : Graphon α μ) (ρ : ℝ) :
    ContinuousOn (dualBoundary μ W) (fractionalCuts μ ρ) := by
  let P := Realization.commonFiniteApproximationSequence
    (fun _ : Fin 1 => W) (fun _ : α => (0 : Fin 1)) measurable_const
  let F : ℕ → CutDual μ → ℝ := fun n =>
    stepBoundaryPolynomial μ ((P n).matrix 0) (P n).mark (P n).measurable_mark
  have hlim : Tendsto (fun n => Graphon.cutNormDiff W ((P n).graphon 0)) atTop (𝓝 0) :=
    Realization.commonFiniteApproximationSequence_tendsto
      (fun _ : Fin 1 => W) (fun _ : α => (0 : Fin 1)) measurable_const 0
  have hu : TendstoUniformlyOn F (dualBoundary μ W) atTop (fractionalCuts μ ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn φ hφ
    rw [Real.dist_eq]
    have heq := stepBoundaryPolynomial_eq μ ((P n).matrix 0) ((P n).matrix_symm 0)
      ((P n).matrix_bounds 0) (P n).mark (P n).measurable_mark hφ
    change |dualBoundary μ W φ - stepBoundaryPolynomial μ ((P n).matrix 0)
      (P n).mark (P n).measurable_mark φ| < ε
    rw [heq]
    exact (fractionalBoundary_cutNormDiff μ W ((P n).graphon 0)
      (clippedDensity μ φ) (clippedDensity_measurable μ φ) (clippedDensity_bounds μ φ)).trans_lt hn
  exact hu.continuousOn (Eventually.of_forall fun n =>
    (stepBoundaryPolynomial_continuous μ ((P n).matrix 0) (P n).mark
      (P n).measurable_mark).continuousOn).frequently

lemma dualBoundary_pos (W : Graphon α μ) (hW : Connected W)
    (htotal : 0 < ∫ p, W.toAEEqFun p ∂μ.prod μ) {ρ : ℝ} (hρ : 0 < ρ)
    {φ : CutDual μ} (hφ : φ ∈ fractionalCuts μ ρ) : 0 < dualBoundary μ W φ := by
  have hmass : (∫ x, clippedDensity μ φ x ∂μ) ∈ Icc ρ (1-ρ) := by
    rw [integral_congr_ae (clippedDensity_eq μ hφ)]
    exact fractionalCuts_density_mass μ hφ
  have hp := fractionalCut_pos W hW htotal (clippedDensity μ φ)
    (clippedDensity_measurable μ φ) (Eventually.of_forall (clippedDensity_bounds μ φ))
    (hρ.trans_le hmass.1) (by linarith [hmass.2])
  convert hp using 1
  congr 1
  unfold dualBoundary fractionalBoundary fractionalCut
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by ring)

/-- Connected graphons have a uniform positive fractional-cut lower bound
for cuts whose masses stay away from zero and one. -/
theorem exists_uniform_fractionalCut_bound (W : Graphon α μ) (hW : Connected W)
    (htotal : 0 < ∫ p, W.toAEEqFun p ∂μ.prod μ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ σ > 0, ∀ f : α → ℝ, Measurable f →
      (∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1) →
      (∫ x, f x ∂μ) ∈ Icc ρ (1-ρ) → σ ≤ fractionalCut W f := by
  have huniform : ∃ σ > 0, ∀ φ ∈ fractionalCuts μ ρ, σ ≤ dualBoundary μ W φ := by
    by_cases hne : (fractionalCuts μ ρ).Nonempty
    · obtain ⟨φ, hφ, hmin⟩ := (fractionalCuts_isCompact μ ρ).exists_isMinOn hne
        (dualBoundary_continuousOn μ W ρ)
      exact ⟨dualBoundary μ W φ, dualBoundary_pos μ W hW htotal hρ hφ, fun ψ hψ => hmin hψ⟩
    · exact ⟨1, zero_lt_one, fun φ hφ => False.elim (hne ⟨φ,hφ⟩)⟩
  obtain ⟨σ, hσ, hbound⟩ := huniform
  refine ⟨σ, hσ, fun f hf hb hmass => ?_⟩
  obtain ⟨φ, hφ, heq⟩ := exists_fractionalCut_dual μ f hf hb hmass
  have hclip : clippedDensity μ φ =ᵐ[μ] f := (clippedDensity_eq μ hφ).trans heq
  have hprod : ∀ᵐ p ∂μ.prod μ,
      clippedDensity μ φ p.1 = f p.1 ∧ clippedDensity μ φ p.2 = f p.2 := by
    filter_upwards [(measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hclip,
      (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hclip] with p hp hq
    exact ⟨hp,hq⟩
  have hboundary : dualBoundary μ W φ = fractionalCut W f := by
    apply integral_congr_ae
    filter_upwards [hprod] with p hp
    rw [hp.1,hp.2]
    ring
  rw [← hboundary]
  exact hbound φ hφ

end ComponentTransfer.Lifting
