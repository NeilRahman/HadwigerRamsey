import Mathlib

open scoped BigOperators Topology ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory Finset Set

namespace ComponentTransfer.Realization

noncomputable def labelIndicator {K : Type*} (a : K) : K → ℝ :=
  Set.indicator {a} (fun _ => 1)

lemma labelIndicator_measurable {K : Type*} [MeasurableSpace K]
    [MeasurableSingletonClass K] (a : K) : Measurable (labelIndicator a) :=
  measurable_const.indicator (measurableSet_singleton a)

lemma labelIndicator_bounds {K : Type*} (a x : K) :
    0 ≤ labelIndicator a x ∧ labelIndicator a x ≤ 1 := by
  classical
  by_cases h : x = a <;> simp [labelIndicator, h]

noncomputable def labelPattern {I V K : Type*} [Fintype I]
    (f : I → V) (a : I → K) (ω : V → K) : ℝ :=
  ∏ i, labelIndicator (a i) (ω (f i))

lemma labelPattern_measurable {I V K : Type*} [Fintype I]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (f : I → V) (a : I → K) : Measurable (labelPattern f a) := by
  apply Finset.measurable_prod
  intro i hi
  exact (labelIndicator_measurable (a i)).comp (measurable_pi_apply (f i))

lemma labelPattern_bounds {I V K : Type*} [Fintype I]
    (f : I → V) (a : I → K) (ω : V → K) :
    0 ≤ labelPattern f a ω ∧ labelPattern f a ω ≤ 1 := by
  constructor
  · exact prod_nonneg (fun i _ => (labelIndicator_bounds (a i) (ω (f i))).1)
  · exact prod_le_one (fun i _ => (labelIndicator_bounds (a i) (ω (f i))).1)
      (fun i _ => (labelIndicator_bounds (a i) (ω (f i))).2)

lemma integral_labelIndicator_eval {V K : Type*} [Fintype V]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : V → Measure K) [∀ v, IsProbabilityMeasure (μ v)] (v : V) (a : K) :
    (∫ ω : V → K, labelIndicator a (ω v) ∂Measure.pi μ) = (μ v).real {a} := by
  rw [← integral_map (measurable_pi_apply v).aemeasurable
    (labelIndicator_measurable a).aestronglyMeasurable,
    (measurePreserving_eval μ v).map_eq]
  simp [labelIndicator]

/-- Injective maps have exactly the product of the prescribed label probabilities. -/
theorem integral_labelPattern_of_injective {I V K : Type*} [Fintype I] [Fintype V]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : V → Measure K) [∀ v, IsProbabilityMeasure (μ v)]
    (f : I → V) (hf : Function.Injective f) (a : I → K) :
    (∫ ω : V → K, labelPattern f a ω ∂Measure.pi μ) = ∏ i, (μ (f i)).real {a i} := by
  have hind : iIndepFun (fun v (ω : V → K) => ω v) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hsub := hind.precomp hf
  have hp := hsub.comp (fun i => labelIndicator (a i)) (fun i => labelIndicator_measurable _)
  calc
    _ = ∏ i, ∫ ω : V → K, labelIndicator (a i) (ω (f i)) ∂Measure.pi μ :=
      hp.integral_fun_prod_eq_prod_integral (fun i =>
        ((labelIndicator_measurable (a i)).comp (measurable_pi_apply (f i))).aestronglyMeasurable)
    _ = _ := by simp_rw [integral_labelIndicator_eval]

/-- Statistics depending on disjoint sets of independently sampled coordinates
are independent, even when their coordinate lists contain repetitions. -/
theorem labelPattern_independent {I V K : Type*} [Fintype I] [Fintype V]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : V → Measure K) [∀ v, IsProbabilityMeasure (μ v)]
    (f g : I → V) (a b : I → K) (hfg : Disjoint (Set.range f) (Set.range g)) :
    IndepFun (labelPattern f a) (labelPattern g b) (Measure.pi μ) := by
  classical
  let S : Finset V := univ.image f
  let T : Finset V := univ.image g
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvS
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hvT
    exact Set.disjoint_left.mp hfg ⟨i,rfl⟩ ⟨j,hji⟩
  let F : (S → K) → ℝ := fun z => ∏ i, labelIndicator (a i) (z ⟨f i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
  let G : (T → K) → ℝ := fun z => ∏ i, labelIndicator (b i) (z ⟨g i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
  have hFm : Measurable F := by
    apply Finset.measurable_prod
    intro i hi
    exact (labelIndicator_measurable _).comp (measurable_pi_apply _)
  have hGm : Measurable G := by
    apply Finset.measurable_prod
    intro i hi
    exact (labelIndicator_measurable _).comp (measurable_pi_apply _)
  have hind : iIndepFun (fun v (ω : V → K) => ω v) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  exact (hind.indepFun_finset S T hST (fun v => measurable_pi_apply v)).comp hFm hGm

end ComponentTransfer.Realization
