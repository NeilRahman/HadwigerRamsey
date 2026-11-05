import HadwigerRamsey.Existence.Sampling
import HadwigerRamsey.Existence.MinorTools

open scoped BigOperators Classical ENNReal
open Set MeasureTheory ProbabilityTheory HadwigerRamsey

namespace ComponentTransfer

/-- Independent categorical sampling allows arbitrary numbers of colours. -/
noncomputable def colourPMF {r : ℕ} (p : Fin r → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) : PMF (Fin r) :=
  PMF.ofFintype (fun c => ENNReal.ofReal (p c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hp c), hs, ENNReal.ofReal_one])

noncomputable def colourMeasure {r : ℕ} (p : Fin r → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) : Measure (Fin r) :=
  (colourPMF p hp hs).toMeasure

instance {r : ℕ} (p : Fin r → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) :
    IsProbabilityMeasure (colourMeasure p hp hs) := by
  unfold colourMeasure
  infer_instance

lemma colourMeasure_singleton {r : ℕ} (p : Fin r → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) (c : Fin r) :
    (colourMeasure p hp hs).real {c} = p c := by
  rw [measureReal_def, colourMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [colourPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp c)]

noncomputable def colourGraph {n r : ℕ} (c : Fin r) (ω : Edge n → Fin r) :
    SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v, ω (Existence.edgeOf u v h) = c
  symm := ⟨by
    intro u v ⟨h, hc⟩
    exact ⟨h.symm, by simpa only [← Existence.edgeOf_symm u v h] using hc⟩⟩
  loopless := ⟨by intro u ⟨h, _⟩; exact h rfl⟩

lemma colourGraph_edge {n r : ℕ} (c : Fin r) (ω : Edge n → Fin r) (e : Edge n) :
    (colourGraph c ω).Adj e.val.1 e.val.2 ↔ ω e = c := by
  have he : Existence.edgeOf e.val.1 e.val.2 (ne_of_lt e.property) = e := by
    apply Subtype.ext
    simp [Existence.edgeOf, min_eq_left e.property.le, max_eq_right e.property.le]
  change (∃ h : e.val.1 ≠ e.val.2, ω (Existence.edgeOf _ _ h) = c) ↔ _
  simp only [he, exists_prop_of_true (ne_of_lt e.property)]

lemma colourGraph_partition {n r : ℕ} (ω : Edge n → Fin r) (u v : Fin n)
    (h : u ≠ v) : ∃! c, (colourGraph c ω).Adj u v := by
  refine ⟨ω (Existence.edgeOf u v h), ⟨h, rfl⟩, ?_⟩
  rintro c ⟨_, hc⟩
  exact hc.symm

noncomputable def labelsMeasure {n r : ℕ} (p : Edge n → Fin r → ℝ)
    (hp : ∀ e c, 0 ≤ p e c) (hs : ∀ e, ∑ c, p e c = 1) :
    Measure (Edge n → Fin r) :=
  Measure.pi (fun e => colourMeasure (p e) (hp e) (hs e))

instance {n r : ℕ} (p : Edge n → Fin r → ℝ)
    (hp : ∀ e c, 0 ≤ p e c) (hs : ∀ e, ∑ c, p e c = 1) :
    IsProbabilityMeasure (labelsMeasure p hp hs) := by
  unfold labelsMeasure
  infer_instance

lemma label_probability {n r : ℕ} (p : Edge n → Fin r → ℝ)
    (hp : ∀ e c, 0 ≤ p e c) (hs : ∀ e, ∑ c, p e c = 1)
    (e : Edge n) (c : Fin r) :
    (labelsMeasure p hp hs).real {ω | ω e = c} = p e c := by
  have hh := (measurePreserving_eval
    (fun e => colourMeasure (p e) (hp e) (hs e)) e).measure_preimage
    (measurableSet_singleton c).nullMeasurableSet
  change (labelsMeasure p hp hs).real (Function.eval e ⁻¹' {c}) = _
  rw [measureReal_def, labelsMeasure, hh]
  exact colourMeasure_singleton _ _ _ _

lemma labels_independent {n r : ℕ} (p : Edge n → Fin r → ℝ)
    (hp : ∀ e c, 0 ≤ p e c) (hs : ∀ e, ∑ c, p e c = 1) (c : Fin r) :
    iIndepSet (fun e => {ω | ω e = c}) (labelsMeasure p hp hs) := by
  have hi : iIndepFun (fun e (ω : Edge n → Fin r) => ω e) (labelsMeasure p hp hs) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  apply (iIndepSet_iff_meas_biInter
    (fun e => (measurable_pi_apply e) (measurableSet_singleton c))).mpr
  intro S
  exact hi.measure_inter_preimage_eq_mul S (sets := fun _ => {c})
    (fun _ _ => measurableSet_singleton c)

/-- The edge events of each colour have exactly the model required by Theorem 1. -/
theorem colour_model {n r : ℕ} (p : Edge n → Fin r → ℝ)
    (hp : ∀ e c, 0 ≤ p e c) (hs : ∀ e, ∑ c, p e c = 1) (c : Fin r) :
    (∀ e : Edge n, MeasurableSet (edgeEvent (colourGraph c) e)) ∧
    iIndepSet (edgeEvent (colourGraph c)) (labelsMeasure p hp hs) ∧
    ∀ e, (labelsMeasure p hp hs).real (edgeEvent (colourGraph c) e) = p e c := by
  have he : edgeEvent (colourGraph (n := n) c) = (fun e => {ω | ω e = c}) := by
    funext e
    ext ω
    exact colourGraph_edge c ω e
  rw [he]
  exact ⟨fun e => (measurable_pi_apply _) (measurableSet_singleton _),
    labels_independent p hp hs c, fun e => label_probability p hp hs e c⟩

/-- A finite union bound, including avoidance of zero-probability edges. -/
theorem exists_all_good {Ω I E : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (Z : E → Set Ω) (hZ : ∀ e, MeasurableSet (Z e))
    {d : ℝ} (hd : Fintype.card I * d < 1)
    (hp : ∀ i, 1-d ≤ μ.real (A i)) (hz : ∀ e, μ.real (Z e) = 0) :
    ∃ ω, (∀ i, ω ∈ A i) ∧ ∀ e, ω ∉ Z e := by
  let B := (⋃ i, (A i)ᶜ) ∪ ⋃ e, Z e
  have hB : MeasurableSet B := (MeasurableSet.iUnion (fun i => (hA i).compl)).union
    (MeasurableSet.iUnion hZ)
  have hzero : μ.real (⋃ e, Z e) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    exact (measureReal_iUnion_fintype_le Z).trans (by simp [hz])
  have hbad : μ.real B ≤ Fintype.card I*d := by
    have hh := measureReal_iUnion_fintype_le (fun i => (A i)ᶜ) (μ := μ)
    have hs : (∑ i, μ.real (A i)ᶜ) ≤ Fintype.card I*d := by
      calc
        _ ≤ ∑ _i : I, d := Finset.sum_le_sum (fun i _ => by
          have hc := measureReal_add_measureReal_compl (μ := μ) (hA i)
          rw [probReal_univ] at hc
          linarith only [hc, hp i])
        _ = _ := by simp
    have hh' := measureReal_union_le (⋃ i, (A i)ᶜ) (⋃ e, Z e) (μ := μ)
    change μ.real B ≤ _ at hh'
    linarith only [hh', hh, hs, hzero]
  have hc := measureReal_add_measureReal_compl (μ := μ) hB
  rw [probReal_univ] at hc
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero
    (show μ.real Bᶜ ≠ 0 by linarith only [hc, hbad, hd])
  refine ⟨ω, ?_, ?_⟩
  · intro i
    by_contra hi
    exact hω (Or.inl (mem_iUnion.mpr ⟨i, hi⟩))
  · intro e he
    exact hω (Or.inr (mem_iUnion.mpr ⟨e, he⟩))

/-- Components may have arbitrary finite sizes and an arbitrary finite label set. -/
theorem hadwigerNumber_le_of_components {n : ℕ} {I : Type*}
    (G : SimpleGraph (Fin n)) (c : Fin n → I) (m : I → ℕ)
    (f : ∀ i, Fin (m i) → Fin n) (hf : ∀ i, Function.Injective (f i))
    (hcover : ∀ i v, c v = i → v ∈ range (f i))
    (hedge : ∀ u v, G.Adj u v → c u = c v) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i, (hadwigerNumber (G.comap (f i)) : ℝ) ≤ R) :
    (hadwigerNumber G : ℝ) ≤ R := by
  by_cases hs : 0 < hadwigerNumber G
  · obtain ⟨t, B, hc, hd, he, hfiber⟩ :=
      (hadwigerNumber_hasCliqueMinor G).in_one_fiber hs c hedge
    have hm := HasCliqueMinor.comap_of_range (f t) (hf t) B hc hd he
      (fun i v hv => hcover t v (hfiber i v hv))
    have hh : hadwigerNumber G ≤ hadwigerNumber (G.comap (f t)) :=
      cliqueMinor_le_hadwigerNumber hm
    exact (show (hadwigerNumber G : ℝ) ≤ hadwigerNumber (G.comap (f t)) by
      exact_mod_cast hh).trans (hb t)
  · have hh : hadwigerNumber G = 0 := by omega
    simpa only [hh, Nat.cast_zero] using hR

end ComponentTransfer
