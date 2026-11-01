import HadwigerRamsey.ThomasonUpper.RandomLabels
import HadwigerRamsey.Measurability

open scoped Classical
open Set MeasureTheory ProbabilityTheory
namespace HadwigerRamsey.Existence

abbrev Label := Option Bool
noncomputable def edgeOf {n : ℕ} (u v : Fin n) (h : u ≠ v) : Edge n :=
  ⟨(min u v,max u v),min_lt_max.mpr h⟩
lemma edgeOf_symm {n : ℕ} (u v : Fin n) (h : u ≠ v) : edgeOf u v h = edgeOf v u h.symm := by
  apply Subtype.ext; simp [edgeOf,min_comm,max_comm]
noncomputable def colourGraph {n : ℕ} (a : Label) (ω : Edge n → Label) : SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v, ω (edgeOf u v h) = a
  symm := ⟨by intro u v ⟨h,ha⟩; exact ⟨h.symm,by simpa only [← edgeOf_symm u v h] using ha⟩⟩
  loopless := ⟨by intro u ⟨h,_⟩; exact h rfl⟩
lemma colourGraph_edge {n : ℕ} (a : Label) (ω : Edge n → Label) (e : Edge n) :
    (colourGraph a ω).Adj e.val.1 e.val.2 ↔ ω e = a := by
  have he : edgeOf e.val.1 e.val.2 (ne_of_lt e.property) = e := by
    apply Subtype.ext
    simp [edgeOf,min_eq_left e.property.le,max_eq_right e.property.le]
  change (∃ h : e.val.1 ≠ e.val.2, ω (edgeOf _ _ h) = a) ↔ _
  simp only [he, exists_prop_of_true (ne_of_lt e.property)]
noncomputable def labelsMeasure {n : ℕ} (r : Edge n → ℝ)
    (hr : ∀ e, 0 ≤ r e) (hrhalf : ∀ e, r e ≤ 1/2) : Measure (Edge n → Label) :=
  Measure.pi (fun e => ThomasonUpper.reservoirLabelMeasure (r e) (hr e) (hrhalf e))
instance {n : ℕ} (r : Edge n → ℝ) (hr : ∀ e, 0 ≤ r e) (hrhalf : ∀ e, r e ≤ 1/2) :
    IsProbabilityMeasure (labelsMeasure r hr hrhalf) := by unfold labelsMeasure; infer_instance
lemma label_probability {n : ℕ} (r : Edge n → ℝ) (hr : ∀ e, 0 ≤ r e) (hrhalf : ∀ e, r e ≤ 1/2)
    (e : Edge n) (a : Label) :
    (labelsMeasure r hr hrhalf).real {ω | ω e = a} = if a = none then 1-2*r e else r e := by
  have hh := (measurePreserving_eval (fun e => ThomasonUpper.reservoirLabelMeasure (r e) (hr e) (hrhalf e)) e).measure_preimage
    (measurableSet_singleton a).nullMeasurableSet
  change (labelsMeasure r hr hrhalf).real (Function.eval e ⁻¹' {a}) = _
  rw [measureReal_def,labelsMeasure,hh]
  exact ThomasonUpper.reservoirLabelMeasure_singleton _ _ _ _
lemma labels_independent {n : ℕ} (r : Edge n → ℝ) (hr : ∀ e, 0 ≤ r e) (hrhalf : ∀ e, r e ≤ 1/2)
    (a : Label) : iIndepSet (fun e => {ω | ω e = a}) (labelsMeasure r hr hrhalf) := by
  have hi : iIndepFun (fun e (ω : Edge n → Label) => ω e) (labelsMeasure r hr hrhalf) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  apply (iIndepSet_iff_meas_biInter (fun e => (measurable_pi_apply e) (measurableSet_singleton a))).mpr
  intro S
  exact hi.measure_inter_preimage_eq_mul S (sets := fun _ => {a}) (fun _ _ => measurableSet_singleton a)

def edgeEmb {n m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (e : Edge m) : Edge n :=
  ⟨(f e.val.1,f e.val.2),hf e.property⟩
lemma edgeEmb_injective {n m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) : Function.Injective (edgeEmb f hf) := by
  intro e d h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact Prod.ext (hf.injective (congrArg Prod.fst hh)) (hf.injective (congrArg Prod.snd hh))
lemma comap_edge_event {n m : ℕ} (a : Label) (f : Fin m → Fin n) (hf : StrictMono f) (e : Edge m) :
    edgeEvent (fun ω => (colourGraph a ω).comap f) e = {ω | ω (edgeEmb f hf e) = a} := by
  ext ω
  exact colourGraph_edge a ω (edgeEmb f hf e)

lemma colour_model {n m : ℕ} (r : Edge n → ℝ) (hr : ∀ e, 0 ≤ r e) (hrhalf : ∀ e, r e ≤ 1/2)
    (a : Label) (f : Fin m → Fin n) (hf : StrictMono f) :
    (∀ e, MeasurableSet (edgeEvent (fun ω => (colourGraph a ω).comap f) e)) ∧
    iIndepSet (edgeEvent (fun ω => (colourGraph a ω).comap f)) (labelsMeasure r hr hrhalf) ∧
    ∀ e, (labelsMeasure r hr hrhalf).real (edgeEvent (fun ω => (colourGraph a ω).comap f) e) =
      if a = none then 1-2*r (edgeEmb f hf e) else r (edgeEmb f hf e) := by
  have he : edgeEvent (fun ω => (colourGraph a ω).comap f) = (fun e => {ω | ω (edgeEmb f hf e) = a}) := funext (comap_edge_event a f hf)
  rw [he]
  exact ⟨fun e => (measurable_pi_apply _) (measurableSet_singleton _),
    iIndepSet.precomp (edgeEmb_injective f hf) (labels_independent r hr hrhalf a),
    fun e => label_probability r hr hrhalf _ a⟩
end HadwigerRamsey.Existence
