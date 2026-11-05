import HadwigerRamsey4Col.LiftingLemma
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped Classical Topology BigOperators unitInterval ENNReal
open MeasureTheory Filter Set
open HadwigerRamsey4Col.Realization HadwigerRamsey4Col.Lifting

namespace HadwigerRamsey4Col.Transfer

/-- A countable component labelling of a coloured graphon. Label zero is
the zero-degree remainder; positive labels have connected restrictions. -/
structure ColoredComponents {r : ℕ} (W : Fin r → GraphonI) where
  label : Fin r → I → ℕ
  measurable_label : ∀ c, Measurable (label c)
  support : ∀ c, ∀ᵐ p ∂(volume : Measure I).prod volume,
    (W c).toAEEqFun p ≠ 0 → label c p.1 = label c p.2 ∧ label c p.1 ≠ 0
  connected : ∀ c t, t ≠ 0 → ∀ hpos : 0 < (volume : Measure I).real ((label c) ⁻¹' {t}),
    letI := cond_probability_of_real_pos (volume : Measure I) ((label c) ⁻¹' {t}) hpos
    Connected (restrictGraphon (W c) ((label c) ⁻¹' {t}))

namespace ColoredComponents

variable {r : ℕ} {W : Fin r → GraphonI} (D : ColoredComponents W)

def mark (x : I) : Fin r → ℕ := fun c => D.label c x

lemma mark_measurable : Measurable D.mark :=
  measurable_pi_iff.mpr D.measurable_label

abbrev Atom := {q : Fin r → ℕ // 0 < (volume : Measure I).real (D.mark ⁻¹' {q})}

def atom (i : D.Atom) : Set I := D.mark ⁻¹' {i.val}

noncomputable def mass (i : D.Atom) : ℝ := (volume : Measure I).real (D.atom i)

lemma atom_measurable (i : D.Atom) : MeasurableSet (D.atom i) :=
  D.mark_measurable (measurableSet_singleton _)

lemma mass_pos (i : D.Atom) : 0 < D.mass i := i.property

lemma atoms_disjoint : Pairwise (fun i j : D.Atom => Disjoint (D.atom i) (D.atom j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun x hx hy => hij (Subtype.ext (hx.symm.trans hy)))

lemma atom_subset (c : Fin r) (i : D.Atom) : D.atom i ⊆ (D.label c) ⁻¹' {i.val c} := by
  intro x hx
  change D.label c x = i.val c
  exact congrFun (show D.mark x = i.val from hx) c

lemma mass_hasSum : HasSum D.mass 1 := by
  let good : Set (Fin r → ℕ) := {q | 0 < (volume : Measure I).real (D.mark ⁻¹' {q})}
  have hbad : (volume : Measure I) (D.mark ⁻¹' goodᶜ) = 0 := by
    apply (measure_preimage_eq_zero_iff_of_countable (Set.to_countable goodᶜ)).mpr
    intro q hq
    apply (measureReal_eq_zero_iff (μ := (volume : Measure I))).mp
    exact le_antisymm (not_lt.mp hq) measureReal_nonneg
  have hgood : ∀ᵐ x ∂(volume : Measure I), x ∈ D.mark ⁻¹' good := by
    rw [ae_iff]
    exact hbad
  have hmeasure : (volume : Measure I) (D.mark ⁻¹' good) = 1 := by
    calc _ = (volume : Measure I) univ := measure_congr (hgood.mono (fun x hx => propext ⟨fun _ => trivial,fun _ => hx⟩))
      _ = 1 := measure_univ
  have hsum := tsum_measure_preimage_singleton (μ := (volume : Measure I))
    (Set.to_countable good) (fun q _ => D.mark_measurable (measurableSet_singleton q))
  rw [hmeasure] at hsum
  have hh := ENNReal.hasSum_toReal (by rw [hsum]; norm_num)
  have hreal : (∑' q : good, ((volume : Measure I) (D.mark ⁻¹' {q.val})).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _), hsum, ENNReal.toReal_one]
  change HasSum (fun q : good => ((volume : Measure I) (D.mark ⁻¹' {q.val})).toReal) 1
  simpa only [hreal] using hh

noncomputable def density (c : Fin r) (i j : D.Atom) : ℝ :=
  Graphon.rectAverage (W c) (D.atom i) (D.atom j)

lemma density_bounds (c : Fin r) (i j : D.Atom) : D.density c i j ∈ Icc (0 : ℝ) 1 :=
  Graphon.rectAverage_mem_Icc _ _ _ (D.atom_measurable i) (D.atom_measurable j)

lemma density_symm (c : Fin r) (i j : D.Atom) : D.density c i j = D.density c j i :=
  Graphon.rectAverage_symm _ _ _ (D.atom_measurable i) (D.atom_measurable j)

lemma atom_measure_ne_zero (i : D.Atom) : (volume : Measure I) (D.atom i) ≠ 0 := by
  intro h
  have hm := D.mass_pos i
  simp [mass, measureReal_def, h] at hm

lemma density_eq (c : Fin r) (i j : D.Atom) : D.density c i j =
    (W c).toSymmKernel.rectIntegral (D.atom i) (D.atom j)/(D.mass i*D.mass j) := by
  rw [density, Graphon.rectAverage, dif_neg (D.atom_measure_ne_zero i),
    dif_neg (D.atom_measure_ne_zero j)]
  change (D.mass i)⁻¹*(D.mass j)⁻¹*_ = _
  rw [div_eq_mul_inv,mul_inv]
  unfold SymmKernel.rectIntegral
  ring

lemma density_sum (hsum : ∀ᵐ p ∂(volume : Measure I).prod volume,
    ∑ c, (W c).toAEEqFun p = 1) (i j : D.Atom) : ∑ c, D.density c i j = 1 := by
  simp_rw [D.density_eq]
  rw [← Finset.sum_div]
  have hint : (∑ c, (W c).toSymmKernel.rectIntegral (D.atom i) (D.atom j)) =
      D.mass i*D.mass j := by
    unfold SymmKernel.rectIntegral
    rw [← integral_finsetSum _ (fun c _ => (SymmKernel.graphon_integrable (W c)).integrableOn)]
    rw [integral_congr_ae (ae_restrict_of_ae hsum), setIntegral_const]
    simp [mass, measureReal_def, ENNReal.toReal_mul, Measure.prod_prod,
      D.atom_measurable i, D.atom_measurable j]
  rw [hint,div_self (mul_ne_zero (D.mass_pos i).ne' (D.mass_pos j).ne')]

lemma density_zero (c : Fin r) (i j : D.Atom)
    (h : i.val c ≠ j.val c ∨ i.val c = 0) : D.density c i j = 0 := by
  rw [D.density_eq]
  have hint : (W c).toSymmKernel.rectIntegral (D.atom i) (D.atom j) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (D.support c),
      ae_restrict_mem ((D.atom_measurable i).prod (D.atom_measurable j))] with p hp hmem
    by_contra hn
    obtain ⟨heq,hne⟩ := hp hn
    have hleft : D.label c p.1 = i.val c := D.atom_subset c i hmem.1
    have hright : D.label c p.2 = j.val c := D.atom_subset c j hmem.2
    rw [hleft,hright] at heq
    rw [hleft] at hne
    rcases h with h | h
    · exact h heq
    · exact hne h
  rw [hint,zero_div]

end ColoredComponents
end HadwigerRamsey4Col.Transfer
