import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open scoped Topology ENNReal RealInnerProductSpace Classical
open MeasureTheory Filter Set

namespace ComponentTransfer.Lifting

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

abbrev CutL2 := Lp ℝ 2 μ
abbrev CutDual := WeakDual ℝ (CutL2 μ)

noncomputable def cutIndicator (A : Set α) (hA : MeasurableSet A) : CutL2 μ :=
  indicatorConstLp 2 hA (measure_ne_top μ A) 1

noncomputable def dualDensity (φ : CutDual μ) : CutL2 μ :=
  (InnerProductSpace.toDual ℝ (CutL2 μ)).symm φ.toStrongDual

lemma dualDensity_setIntegral (φ : CutDual μ) (A : Set α) (hA : MeasurableSet A) :
    ∫ x in A, dualDensity μ φ x ∂μ = φ (cutIndicator μ A hA) := by
  rw [← L2.inner_indicatorConstLp_one hA (measure_ne_top μ A), real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

/-- The weak-star compact set of fractional cuts of prescribed balanced mass.
The inequalities against all measurable indicators encode precisely density
values between zero and one. -/
def fractionalCuts (ρ : ℝ) : Set (CutDual μ) :=
  {φ | φ.toStrongDual ∈ Metric.closedBall 0 1 ∧
    (∀ A (hA : MeasurableSet A), 0 ≤ φ (cutIndicator μ A hA) ∧
      φ (cutIndicator μ A hA) ≤ μ.real A) ∧
    ρ ≤ φ (cutIndicator μ Set.univ MeasurableSet.univ) ∧
      φ (cutIndicator μ Set.univ MeasurableSet.univ) ≤ 1-ρ}

lemma fractionalCuts_isCompact (ρ : ℝ) : IsCompact (fractionalCuts μ ρ) := by
  have hclosed : IsClosed {φ : CutDual μ |
      (∀ A (hA : MeasurableSet A), 0 ≤ φ (cutIndicator μ A hA) ∧
        φ (cutIndicator μ A hA) ≤ μ.real A) ∧
      ρ ≤ φ (cutIndicator μ Set.univ MeasurableSet.univ) ∧
        φ (cutIndicator μ Set.univ MeasurableSet.univ) ≤ 1-ρ} := by
    apply IsClosed.inter
    · have hlo (A : Set α) (hA : MeasurableSet A) :
          IsClosed {φ : CutDual μ | 0 ≤ φ (cutIndicator μ A hA)} :=
        isClosed_le continuous_const (WeakDual.eval_continuous _)
      have hhi (A : Set α) (hA : MeasurableSet A) :
          IsClosed {φ : CutDual μ | φ (cutIndicator μ A hA) ≤ μ.real A} :=
        isClosed_le (WeakDual.eval_continuous _) continuous_const
      have hh := isClosed_iInter (fun A : Set α => isClosed_iInter
        (fun hA : MeasurableSet A => (hlo A hA).inter (hhi A hA)))
      have hset : {φ : CutDual μ | ∀ A (hA : MeasurableSet A),
          0 ≤ φ (cutIndicator μ A hA) ∧ φ (cutIndicator μ A hA) ≤ μ.real A} =
          ⋂ A, ⋂ hA : MeasurableSet A,
            {φ : CutDual μ | 0 ≤ φ (cutIndicator μ A hA)} ∩
              {φ : CutDual μ | φ (cutIndicator μ A hA) ≤ μ.real A} := by
        ext φ
        simp
      rwa [← hset] at hh
    · exact (isClosed_le continuous_const (WeakDual.eval_continuous _)).inter
        (isClosed_le (WeakDual.eval_continuous _) continuous_const)
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℝ (CutL2 μ)) 1).inter_right hclosed

lemma dualDensity_integrable (φ : CutDual μ) : Integrable (dualDensity μ φ) μ :=
  memLp_one_iff_integrable.mp ((Lp.memLp (dualDensity μ φ)).mono_exponent (by norm_num))

lemma fractionalCuts_density_bounds {ρ : ℝ} {φ : CutDual μ} (hφ : φ ∈ fractionalCuts μ ρ) :
    ∀ᵐ x ∂μ, dualDensity μ φ x ∈ Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ᵐ[μ] dualDensity μ φ :=
    ae_nonneg_of_forall_setIntegral_nonneg (dualDensity_integrable μ φ)
      (fun A hA _ => by rw [dualDensity_setIntegral]; exact (hφ.2.1 A hA).1)
  have hle : dualDensity μ φ ≤ᵐ[μ] (fun _ => (1 : ℝ)) :=
    ae_le_of_forall_setIntegral_le (dualDensity_integrable μ φ) (integrable_const 1)
      (fun A hA _ => by
        rw [dualDensity_setIntegral]
        simpa using (hφ.2.1 A hA).2)
  filter_upwards [hnonneg, hle] with x hx hy
  exact ⟨hx, hy⟩

lemma fractionalCuts_density_mass {ρ : ℝ} {φ : CutDual μ} (hφ : φ ∈ fractionalCuts μ ρ) :
    (∫ x, dualDensity μ φ x ∂μ) ∈ Icc ρ (1-ρ) := by
  have h := dualDensity_setIntegral μ φ Set.univ MeasurableSet.univ
  rw [setIntegral_univ] at h
  rw [h]
  exact hφ.2.2

noncomputable def functionDual (f : CutL2 μ) : CutDual μ :=
  StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ (CutL2 μ)) f)

lemma dualDensity_functionDual (f : CutL2 μ) : dualDensity μ (functionDual μ f) = f := by
  exact (InnerProductSpace.toDual ℝ (CutL2 μ)).symm_apply_apply f

lemma exists_fractionalCut_dual {ρ : ℝ} (f : α → ℝ) (hf : Measurable f)
    (hb : ∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1)
    (hmass : (∫ x, f x ∂μ) ∈ Icc ρ (1-ρ)) :
    ∃ φ ∈ fractionalCuts μ ρ, dualDensity μ φ =ᵐ[μ] f := by
  have hnorm : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := hb.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hfLp : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable 1 hnorm
  let F := hfLp.toLp f
  let φ := functionDual μ F
  have hFeq : dualDensity μ φ =ᵐ[μ] f := by
    rw [dualDensity_functionDual]
    exact hfLp.coeFn_toLp
  have heval (A : Set α) (hA : MeasurableSet A) :
      φ (cutIndicator μ A hA) = ∫ x in A, f x ∂μ := by
    rw [← dualDensity_setIntegral]
    exact integral_congr_ae (ae_restrict_of_ae hFeq)
  have hfi : Integrable f μ := Integrable.of_mem_Icc 0 1 hf.aemeasurable hb
  refine ⟨φ, ⟨?_, ?_, ?_⟩, hFeq⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(InnerProductSpace.toDual ℝ (CutL2 μ)) F‖ ≤ 1
    rw [(InnerProductSpace.toDual ℝ (CutL2 μ)).norm_map]
    have hFbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ 1 := by
      filter_upwards [hfLp.coeFn_toLp, hnorm] with x hx hb
      rwa [hx]
    simpa [measureUnivNNReal, probReal_univ] using Lp.norm_le_of_ae_bound (f := F) zero_le_one hFbound
  · intro A hA
    rw [heval A hA]
    constructor
    · exact setIntegral_nonneg_of_ae (hb.mono fun x hx => hx.1)
    · have hh : (∫ x in A, f x ∂μ) ≤ ∫ _ in A, (1 : ℝ) ∂μ := setIntegral_mono_ae_restrict hfi.integrableOn (integrable_const (1 : ℝ)).integrableOn
        (ae_restrict_of_ae (hb.mono fun x hx => hx.2))
      simpa using hh
  · simpa only [heval Set.univ MeasurableSet.univ, setIntegral_univ, Set.mem_Icc] using hmass

end ComponentTransfer.Lifting
