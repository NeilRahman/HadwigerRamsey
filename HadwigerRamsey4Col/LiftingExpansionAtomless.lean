import HadwigerRamsey4Col.LiftingExpansionPositive
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.ConditionalProbability

open scoped Classical Topology unitInterval
open MeasureTheory ProbabilityTheory Filter Set

namespace HadwigerRamsey4Col.Lifting

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Conditional restriction preserves zero mass of singletons. -/
theorem cond_nullSingletonClass [NullSingletonClass μ] (S : Set α) :
    NullSingletonClass (cond μ S) := by
  constructor
  intro x
  exact cond_absolutelyContinuous (measure_singleton x)

/-- An injective coordinate on a probability space with null singletons
cannot be almost everywhere constant. -/
theorem not_ae_eq_const_of_injective [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (coord : α → ℝ) (hinj : Function.Injective coord) (m : ℝ) :
    ¬ coord =ᵐ[μ] (fun _ => m) := by
  intro heq
  have hsub : {x | coord x = m}.Subsingleton := by
    intro x hx y hy
    exact hinj (hx.trans hy.symm)
  have hz := hsub.measure_zero μ
  have hneq : ∀ᵐ x ∂μ, coord x ≠ m := by
    rw [ae_iff]
    simpa only [not_not] using hz
  have hfalse : ∀ᵐ x ∂μ, False := by
    filter_upwards [heq,hneq] with x hx hn
    exact hn hx
  exact hfalse.exists.choose_spec

/-- Thresholding a nonconstant integrable real coordinate produces a
measurable set with mass strictly between zero and one. -/
theorem exists_nontrivial_measurable_set_of_coordinate [IsProbabilityMeasure μ]
    (coord : α → ℝ) (hcoord : Measurable coord) (hci : Integrable coord μ)
    (hnonconst : ∀ m : ℝ, ¬ coord =ᵐ[μ] (fun _ => m)) :
    ∃ A : Set α, MeasurableSet A ∧ 0 < μ.real A ∧ μ.real A < 1 := by
  let m := ∫ x, coord x ∂μ
  let A : Set α := {x | m < coord x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hcoord
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  have hA1 : μ.real A ≤ 1 := measureReal_le_one
  have hzero : μ.real A ≠ 0 := by
    intro hzero
    have hz : μ A = 0 := (measureReal_eq_zero_iff (μ := μ)).mp hzero
    have hevent : ∀ᵐ x ∂μ, x ∉ A := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hz
    have hle : coord ≤ᵐ[μ] fun _ => m := hevent.mono (fun x hx => le_of_not_gt hx)
    apply hnonconst m
    apply (integral_eq_iff_of_ae_le hci (integrable_const m) hle).mp
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  have hone : μ.real A ≠ 1 := by
    intro hone
    have hz : μ Aᶜ = 0 := by
      apply (measureReal_eq_zero_iff (μ := μ)).mp
      rw [probReal_compl_eq_one_sub hA, hone]
      ring
    have hevent : ∀ᵐ x ∂μ, x ∈ A := by
      rw [ae_iff]
      exact hz
    have hle : (fun _ => m) ≤ᵐ[μ] coord := hevent.mono (fun x hx => le_of_lt hx)
    apply hnonconst m
    apply EventuallyEq.symm
    apply (integral_eq_iff_of_ae_le (integrable_const m) hci hle).mp
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  exact ⟨A,hA,lt_of_le_of_ne hA0 (Ne.symm hzero),lt_of_le_of_ne hA1 hone⟩

/-- Connectedness forces positive total edge mass whenever the carrier has a
measurable injective integrable coordinate and null singleton masses. -/
theorem Connected.integral_pos_of_injective [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (W : Graphon α μ) (hW : Connected W) (coord : α → ℝ)
    (hcoord : Measurable coord) (hci : Integrable coord μ) (hinj : Function.Injective coord) :
    0 < ∫ p, W.toAEEqFun p ∂μ.prod μ := by
  obtain ⟨A,hA,hA0,hA1⟩ := exists_nontrivial_measurable_set_of_coordinate coord hcoord hci
    (not_ae_eq_const_of_injective coord hinj)
  have hc := hW A hA hA0 hA1
  apply hc.trans_le
  exact setIntegral_le_integral (SymmKernel.graphon_integrable W)
    (W.ae_mem_Icc.mono (fun _ hp => hp.1))

/-- The unit-interval coordinate is bounded, so this applies to Lebesgue
measure and every positive normalized measurable restriction of it. -/
theorem Connected.integral_pos_unitInterval {ν : Measure I} [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (W : Graphon I ν) (hW : Connected W) :
    0 < ∫ p, W.toAEEqFun p ∂ν.prod ν := by
  apply hW.integral_pos_of_injective W (fun x : I => (x : ℝ)) measurable_subtype_coe
  · exact Integrable.of_mem_Icc 0 1 measurable_subtype_coe.aemeasurable
      (Eventually.of_forall fun x => x.property)
  · exact Subtype.val_injective

end HadwigerRamsey4Col.Lifting
