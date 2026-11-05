import HadwigerRamsey4Col.RealizationCells
import HadwigerRamsey4Col.RealizationConvergenceTransport

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set Finset

namespace HadwigerRamsey4Col.Realization

variable {α β K : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype K] [DecidableEq K] [MeasurableSpace K] [MeasurableSingletonClass K]
  (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Conditioning on a null cell uses the original probability measure.
Such cells receive zero transport mass. -/
noncomputable def conditionalOrSelf (A : Set α) : Measure α :=
  if μ A = 0 then μ else ProbabilityTheory.cond μ A

instance conditionalOrSelf_probability (A : Set α) :
    IsProbabilityMeasure (conditionalOrSelf μ A) := by
  unfold conditionalOrSelf
  split_ifs with h
  · infer_instance
  · exact cond_isProbabilityMeasure h

lemma mass_smul_conditionalOrSelf (A : Set α) :
    μ A • conditionalOrSelf μ A = μ.restrict A := by
  by_cases h : μ A = 0
  · simp [conditionalOrSelf, h, Measure.restrict_eq_zero.mpr h]
  · simp only [conditionalOrSelf, if_neg h, ProbabilityTheory.cond, smul_smul]
    rw [ENNReal.mul_inv_cancel h (measure_ne_top μ A), one_smul]

lemma conditionalOrSelf_support (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0) :
    ∀ᵐ x ∂conditionalOrSelf μ A, x ∈ A := by
  simpa only [conditionalOrSelf, if_neg hpos] using (ae_cond_mem (μ := μ) hA)

lemma sum_fibre_measureReal (mark : α → K) (hmark : Measurable mark) :
    ∑ i, μ.real (mark ⁻¹' {i}) = 1 := by
  have hd : Pairwise (fun i j : K => Disjoint (mark ⁻¹' {i}) (mark ⁻¹' {j})) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj => hij (hi.symm.trans hj))
  have hcov : (⋃ i : K, mark ⁻¹' {i}) = Set.univ := by ext x; simp
  have hs := measureReal_iUnion_fintype (μ := μ) hd
    (fun i => hmark (measurableSet_singleton _))
  rw [hcov] at hs
  simpa using hs.symm

lemma conditionalOrSelf_decomposition (mark : α → K) (hmark : Measurable mark) :
    (∑ i, ENNReal.ofReal (μ.real (mark ⁻¹' {i})) •
      conditionalOrSelf μ (mark ⁻¹' {i})) = μ := by
  simp_rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _),
    mass_smul_conditionalOrSelf]
  have hd : Pairwise (fun i j : K => Disjoint (mark ⁻¹' {i}) (mark ⁻¹' {j})) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj => hij (hi.symm.trans hj))
  have hcov : (⋃ i : K, mark ⁻¹' {i}) = Set.univ := by ext x; simp
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd
    (fun i => hmark (measurableSet_singleton _)), hcov, Measure.restrict_univ]

/-- Lift a finite mass transport by independently conditioning on its two cells. -/
noncomputable def liftedTransport (left : α → K) (right : β → K)
    (q : K → K → ℝ) : Measure (α × β) :=
  ∑ i, ∑ j, ENNReal.ofReal (q i j) •
    (conditionalOrSelf μ (left ⁻¹' {i})).prod
      (conditionalOrSelf ν (right ⁻¹' {j}))

private lemma map_fintype_sum {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype I] (ρ : I → Measure X) (f : X → Y) (hf : Measurable f) :
    (∑ i, ρ i).map f = ∑ i, (ρ i).map f := by
  simp [← Measure.mapₗ_apply_of_measurable hf]

theorem liftedTransport_fst (left : α → K) (hleft : Measurable left)
    (right : β → K) (q : K → K → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = μ.real (left ⁻¹' {i})) :
    (liftedTransport μ ν left right q).map Prod.fst = μ := by
  unfold liftedTransport
  simp_rw [map_fintype_sum _ _ measurable_fst, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul, ← Finset.sum_smul,
    ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq _ j), hrow]
  exact conditionalOrSelf_decomposition μ left hleft

theorem liftedTransport_snd (left : α → K) (right : β → K) (hright : Measurable right)
    (q : K → K → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (hcol : ∀ j, ∑ i, q i j = ν.real (right ⁻¹' {j})) :
    (liftedTransport μ ν left right q).map Prod.snd = ν := by
  unfold liftedTransport
  rw [Finset.sum_comm]
  simp_rw [map_fintype_sum _ _ measurable_snd, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul, ← Finset.sum_smul,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq i _), hcol]
  exact conditionalOrSelf_decomposition ν right hright

theorem liftedTransport_probability (left : α → K) (hleft : Measurable left)
    (right : β → K) (q : K → K → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = μ.real (left ⁻¹' {i})) :
    IsProbabilityMeasure (liftedTransport μ ν left right q) := by
  have hm := liftedTransport_fst μ ν left hleft right q hq hrow
  apply isProbabilityMeasure_iff.mpr
  have h := congrArg (fun ρ : Measure α => ρ Set.univ) hm
  simpa [Measure.map_apply measurable_fst] using h

lemma liftedTransport_real_apply (left : α → K) (right : β → K)
    (q : K → K → ℝ) (hq : ∀ i j, 0 ≤ q i j) (S : Set (α × β)) :
    (liftedTransport μ ν left right q).real S =
      ∑ i, ∑ j, q i j *
        ((conditionalOrSelf μ (left ⁻¹' {i})).prod
          (conditionalOrSelf ν (right ⁻¹' {j}))).real S := by
  simp only [measureReal_def, liftedTransport, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (by
    intro i hi
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_sum (by
    intro j hj
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hq i j)]

lemma liftedTransport_diagonal_disagreement (left : α → K) (hleft : Measurable left)
    (right : β → K) (hright : Measurable right)
    (q : K → K → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = μ.real (left ⁻¹' {i}))
    (hcol : ∀ j, ∑ i, q i j = ν.real (right ⁻¹' {j})) (i : K) :
    q i i * ((conditionalOrSelf μ (left ⁻¹' {i})).prod
      (conditionalOrSelf ν (right ⁻¹' {i}))).real
        {z : α × β | left z.1 ≠ right z.2} = 0 := by
  by_cases hz : q i i = 0
  · rw [hz, zero_mul]
  have hl : q i i ≤ μ.real (left ⁻¹' {i}) := by
    rw [← hrow]
    exact Finset.single_le_sum (fun j _ => hq i j) (Finset.mem_univ i)
  have hr : q i i ≤ ν.real (right ⁻¹' {i}) := by
    rw [← hcol]
    exact Finset.single_le_sum (fun j _ => hq j i) (Finset.mem_univ i)
  have hlpos : μ (left ⁻¹' {i}) ≠ 0 := by
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hl
    exact hz (le_antisymm hl (hq i i))
  have hrpos : ν (right ⁻¹' {i}) ≠ 0 := by
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hr
    exact hz (le_antisymm hr (hq i i))
  have ha := conditionalOrSelf_support μ _ (hleft (measurableSet_singleton _)) hlpos
  have hb := conditionalOrSelf_support ν _ (hright (measurableSet_singleton _)) hrpos
  have hp := (measurePreserving_fst (μ := conditionalOrSelf μ (left ⁻¹' {i}))
    (ν := conditionalOrSelf ν (right ⁻¹' {i}))).quasiMeasurePreserving.ae ha
  have hq' := (measurePreserving_snd (μ := conditionalOrSelf μ (left ⁻¹' {i}))
    (ν := conditionalOrSelf ν (right ⁻¹' {i}))).quasiMeasurePreserving.ae hb
  have hnull : ((conditionalOrSelf μ (left ⁻¹' {i})).prod
      (conditionalOrSelf ν (right ⁻¹' {i}))) {z : α × β | left z.1 ≠ right z.2} = 0 := by
    rw [← ae_iff]
    filter_upwards [hp, hq'] with z hzl hzr
    exact hzl.trans hzr.symm
  rw [measureReal_def, hnull, ENNReal.toReal_zero, mul_zero]

theorem liftedTransport_disagreement_le (left : α → K) (hleft : Measurable left)
    (right : β → K) (hright : Measurable right)
    (q : K → K → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = μ.real (left ⁻¹' {i}))
    (hcol : ∀ j, ∑ i, q i j = ν.real (right ⁻¹' {j})) :
    (liftedTransport μ ν left right q).real {z : α × β | left z.1 ≠ right z.2} ≤
      ∑ i, ∑ j, if i ≠ j then q i j else 0 := by
  rw [liftedTransport_real_apply μ ν left right q hq]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simp only [ne_eq, not_true_eq_false, if_false]
    exact (liftedTransport_diagonal_disagreement μ ν left hleft right hright q hq
      hrow hcol i).le
  · rw [if_pos hij]
    exact mul_le_of_le_one_right (hq i j) measureReal_le_one

/-- Close finite mark frequencies have a common probability coupling whose
mark disagreement is bounded by their total coordinate discrepancy. -/
theorem exists_mark_coupling (left : α → K) (hleft : Measurable left)
    (right : β → K) (hright : Measurable right) :
    ∃ π : Measure (α × β), IsProbabilityMeasure π ∧
      MeasurePreserving Prod.fst π μ ∧ MeasurePreserving Prod.snd π ν ∧
      π.real {z : α × β | left z.1 ≠ right z.2} ≤
        ∑ i, |μ.real (left ⁻¹' {i}) - ν.real (right ⁻¹' {i})| := by
  let p := fun i => μ.real (left ⁻¹' {i})
  let q := fun i => ν.real (right ⁻¹' {i})
  have hsum : ∑ i, p i = ∑ i, q i := by
    rw [sum_fibre_measureReal μ left hleft, sum_fibre_measureReal ν right hright]
  have hnn := finiteTransport_nonneg p q (fun _ => measureReal_nonneg)
    (fun _ => measureReal_nonneg)
  have hrow := finiteTransport_row p q hsum
  have hcol := finiteTransport_column p q hsum
  refine ⟨liftedTransport μ ν left right (finiteTransport p q),
    liftedTransport_probability μ ν left hleft right _ hnn hrow,
    ⟨measurable_fst, liftedTransport_fst μ ν left hleft right _ hnn hrow⟩,
    ⟨measurable_snd, liftedTransport_snd μ ν left right hright _ hnn hcol⟩, ?_⟩
  exact (liftedTransport_disagreement_le μ ν left hleft right hright _ hnn hrow hcol).trans
    (finiteTransport_disagreement_le p q hsum)

end HadwigerRamsey4Col.Realization
