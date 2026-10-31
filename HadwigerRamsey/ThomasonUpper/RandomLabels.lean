import Mathlib

open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory

namespace HadwigerRamsey.ThomasonUpper

instance : MeasurableSpace (Option Bool) := ⊤
instance : DiscreteMeasurableSpace (Option Bool) := ⟨fun _ => trivial⟩

/-- The three labels C, D, and R used in A.5, with probabilities r,r,1-2r. -/
noncomputable def reservoirLabelPMF (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) : PMF (Option Bool) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i = none then 1-2*r else r)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (by
      intro i _
      split_ifs <;> linarith)]
    have hs : (∑ i : Option Bool, if i = none then 1-2*r else r) = 1 := by
      simp [Fintype.sum_option]
    rw [hs, ENNReal.ofReal_one])

noncomputable def reservoirLabelMeasure (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    Measure (Option Bool) := (reservoirLabelPMF r hr hrhalf).toMeasure

instance reservoirLabelMeasure_probability (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    IsProbabilityMeasure (reservoirLabelMeasure r hr hrhalf) := by
  unfold reservoirLabelMeasure
  infer_instance

theorem reservoirLabelMeasure_singleton (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (a : Option Bool) :
    (reservoirLabelMeasure r hr hrhalf).real {a} =
      if a = none then 1-2*r else r := by
  rw [measureReal_def, reservoirLabelMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [reservoirLabelPMF, PMF.ofFintype_apply]
  apply ENNReal.toReal_ofReal
  split_ifs <;> linarith

/-- Independent labels on all vertices. -/
noncomputable def randomLabels {V : Type*} [Fintype V]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) : Measure (V → Option Bool) :=
  Measure.pi (fun _ => reservoirLabelMeasure r hr hrhalf)

instance randomLabels_probability {V : Type*} [Fintype V]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    IsProbabilityMeasure (randomLabels (V := V) r hr hrhalf) := by
  unfold randomLabels
  infer_instance

theorem randomLabels_probability_label {V : Type*} [Fintype V]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (v : V) (a : Option Bool) :
    (randomLabels (V := V) r hr hrhalf).real {ω | ω v = a} =
      if a = none then 1-2*r else r := by
  have hh := (measurePreserving_eval (fun _ : V => reservoirLabelMeasure r hr hrhalf) v).measure_preimage
    (measurableSet_singleton a).nullMeasurableSet
  change (randomLabels r hr hrhalf).real (Function.eval v ⁻¹' {a}) = _
  rw [measureReal_def, randomLabels, hh]
  exact reservoirLabelMeasure_singleton r hr hrhalf a

theorem randomLabels_independent {V : Type*} [Fintype V]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (a : Option Bool) :
    iIndepSet (fun v : V => {ω : V → Option Bool | ω v = a}) (randomLabels r hr hrhalf) := by
  have hi : iIndepFun (fun v (ω : V → Option Bool) => ω v) (randomLabels r hr hrhalf) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  apply (iIndepSet_iff_meas_biInter (fun v => (measurable_pi_apply v) (measurableSet_singleton a))).mpr
  intro S
  exact hi.measure_inter_preimage_eq_mul S (sets := fun _ => {a})
    (fun _ _ => measurableSet_singleton a)

end HadwigerRamsey.ThomasonUpper
