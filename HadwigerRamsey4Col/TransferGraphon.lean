import HadwigerRamsey4Col.TransferAtoms
import HadwigerRamsey4Col.TransferOptimizationExtended

open scoped Classical Topology BigOperators unitInterval ENNReal
open MeasureTheory Filter Set Real
open HadwigerRamsey HadwigerRamsey4Col.Realization HadwigerRamsey4Col.Lifting

namespace HadwigerRamsey4Col.Transfer

lemma normalized_liminf_le {r : ℕ} (N : ℕ → ℕ)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) {B : ℝ}
    (hB : ∀ n c, (hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ) ≤ B)
    (c : Fin r) : Filter.liminf (fun n => ENNReal.ofReal
      ((hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ))) atTop ≤ ENNReal.ofReal B := by
  apply Filter.liminf_le_of_frequently_le'
  exact (Eventually.of_forall (fun n => ENNReal.ofReal_le_ofReal (hB n c))).frequently

namespace ColoredComponents

variable {r : ℕ} {W : Fin r → GraphonI} (D : ColoredComponents W)

lemma finite_same_label_entropy_le (hr : 2 ≤ r) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (hconv : FiniteGraphCommonCutConverges (volume : Measure I) N G W) {B : ℝ}
    (hB : 0 ≤ B)
    (hupper : ∀ n c, (hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ) ≤ B)
    (k : ℕ) (f : Fin k → D.Atom) (hf : Function.Injective f) (c : Fin r)
    (hsame : ∀ i j, (f i).val c = (f j).val c) :
    entropyRoot (D.mass ∘ f) (fun i j => D.density c (f i) (f j)) ≤ ENNReal.ofReal B := by
  by_cases hk : 0 < k
  · let i₀ : Fin k := ⟨0,hk⟩
    let t : ℕ := (f i₀).val c
    have hall (i : Fin k) : (f i).val c = t := hsame i i₀
    by_cases ht : t = 0
    · have hd (i j : Fin k) : D.density c (f i) (f j) = 0 :=
        D.density_zero c (f i) (f j) (Or.inr ((hall i).trans ht))
      simp only [entropyRoot, extendedEnergy, hd, extendedCost]
      simp
    · let S : Set I := (D.label c) ⁻¹' {t}
      have hS : MeasurableSet S := D.measurable_label c (measurableSet_singleton t)
      have hsub (i : Fin k) : D.atom (f i) ⊆ S := by
        simpa only [hall i] using D.atom_subset c (f i)
      have hSpos : 0 < (volume : Measure I).real S :=
        (D.mass_pos (f i₀)).trans_le (measureReal_mono (hsub i₀) (measure_ne_top _ _))
      have hconn := D.connected c t ht hSpos
      have h := lemma8 hr N hN G W hconv c S hS hSpos hconn
        (D.atom ∘ f) (fun i => D.atom_measurable (f i))
        (fun i j hij => D.atoms_disjoint (hf.ne hij)) hsub (fun i => D.mass_pos (f i))
      have hh : entropyRoot (D.mass ∘ f) (fun i j => D.density c (f i) (f j)) ≤
          Filter.liminf (fun n => ENNReal.ofReal
            ((hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ))) atTop := by
        simpa only [Function.comp_def, D.density_eq, mass] using h
      exact hh.trans (normalized_liminf_le N G hupper c)
  · have hk0 : k = 0 := by omega
    subst k
    simp [entropyRoot, extendedEnergy]

include D

/-- Every coloured graphon limit with uniformly bounded normalized minor
numbers yields an admissible countable component model below the same bound. -/
theorem beta_le_of_bounded_sequence (hr : 2 ≤ r)
    (hsum : ∀ᵐ p ∂(volume : Measure I).prod volume, ∑ c, (W c).toAEEqFun p = 1)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (hconv : FiniteGraphCommonCutConverges (volume : Measure I) N G W) {B : ℝ}
    (hB : 0 ≤ B)
    (hupper : ∀ n c, (hadwigerNumber (G n c) : ℝ)*sqrt (log (N n : ℝ))/(N n : ℝ) ≤ B) :
    beta r ≤ B := by
  let E : CountableComponentModel r D.Atom := {
    mass := D.mass
    mass_pos := D.mass_pos
    mass_sum := D.mass_hasSum
    label := fun c i => i.val c
    density := D.density
    density_nonneg := fun c i j => (D.density_bounds c i j).1
    density_le_one := fun c i j => (D.density_bounds c i j).2
    density_symm := D.density_symm
    density_sum := D.density_sum hsum
    density_zero := fun c i j h => D.density_zero c i j (Or.inl h) }
  exact beta_le_of_extended_component_bounds hr E hB
    (D.finite_same_label_entropy_le hr N hN G hconv hB hupper)

end ColoredComponents
end HadwigerRamsey4Col.Transfer
