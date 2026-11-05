import HadwigerRamsey4Col.TransferOptimization

open scoped BigOperators Classical Topology ENNReal
open Filter Finset Real

namespace HadwigerRamsey4Col.Transfer

/-- The countable component data before the singular density-one case has
been excluded. Finite entropy bounds will force every entry below one. -/
structure CountableComponentModel (r : ℕ) (I : Type*) where
  mass : I → ℝ
  mass_pos : ∀ i, 0 < mass i
  mass_sum : HasSum mass 1
  label : Fin r → I → ℕ
  density : Fin r → I → I → ℝ
  density_nonneg : ∀ c i j, 0 ≤ density c i j
  density_le_one : ∀ c i j, density c i j ≤ 1
  density_symm : ∀ c i j, density c i j = density c j i
  density_sum : ∀ i j, ∑ c, density c i j = 1
  density_zero : ∀ c i j, label c i ≠ label c j → density c i j = 0

/-- A finite upper bound for every same-label entropy test excludes a
singular density-one entry. -/
theorem density_lt_one_of_entropy_bounds {r : ℕ} {I : Type*}
    (D : CountableComponentModel r I) {B : ℝ}
    (henergy : ∀ k : ℕ, ∀ f : Fin k → I, Function.Injective f → ∀ c,
      (∀ i j, D.label c (f i) = D.label c (f j)) →
      Lifting.entropyRoot (D.mass ∘ f) (fun i j => D.density c (f i) (f j)) ≤
        ENNReal.ofReal B) :
    ∀ c i j, D.density c i j < 1 := by
  classical
  intro c i j
  by_contra hnot
  have hij : D.density c i j = 1 := le_antisymm (D.density_le_one c i j) (le_of_not_gt hnot)
  have hlabel : D.label c i = D.label c j := by
    by_contra hne
    have hz := D.density_zero c i j hne
    linarith
  let s : Finset I := {i,j}
  let f : Fin s.card → I := fun a => (s.equivFin.symm a).val
  have hf : Function.Injective f := Subtype.val_injective.comp s.equivFin.symm.injective
  have hall (a : Fin s.card) : D.label c (f a) = D.label c i := by
    have ha : f a ∈ s := (s.equivFin.symm a).property
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · rw [ha]
    · rw [ha,hlabel]
  let ai : Fin s.card := s.equivFin ⟨i,by simp [s]⟩
  let aj : Fin s.card := s.equivFin ⟨j,by simp [s]⟩
  have hai : f ai = i := by simp [f,ai]
  have haj : f aj = j := by simp [f,aj]
  have hroot := Lifting.entropyRoot_eq_top_of_density_one (D.mass ∘ f)
    (fun a b => D.density c (f a) (f b)) (fun a => D.mass_pos (f a)) ai aj
    (by simpa only [hai,haj] using hij)
  have hb := henergy s.card f hf c (fun a b => (hall a).trans (hall b).symm)
  rw [hroot] at hb
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hb)

lemma entropyRoot_eq_of_lt_one {K : Type*} [Fintype K]
    (u : K → ℝ) (p : K → K → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hp0 : ∀ i j, 0 ≤ p i j) (hp1 : ∀ i j, p i j < 1) :
    Lifting.entropyRoot u p = ENNReal.ofReal
      (sqrt (∑ i, ∑ j, u i*u j*(-log (1-p i j)))) := by
  obtain ⟨δ,hδ,hδ1,hcap⟩ := Lifting.finite_positive_lower_bound
    (fun q : K × K => 1-p q.1 q.2) (fun q => sub_pos.mpr (hp1 _ _))
  rw [Lifting.entropyRoot_eq_capped u p hδ hδ1 hu hp0 hp1 (fun i j => hcap (i,j))]
  congr 2
  unfold Lifting.cappedEnergy Lifting.cappedCost
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [min_eq_left (by linarith [hcap (i,j)])]

lemma entropyRoot_eq_zero_of_density_zero {K : Type*} [Fintype K]
    (u : K → ℝ) (p : K → K → ℝ) (hp : ∀ i j, p i j = 0) :
    Lifting.entropyRoot u p = 0 := by
  simp [Lifting.entropyRoot, Lifting.extendedEnergy, Lifting.extendedCost, hp]

/-- Countable component optimization with the exact extended entropy bounds
provided by Lemma 8, including automatic exclusion of density one. -/
theorem beta_le_of_extended_component_bounds {r : ℕ} (hr : 2 ≤ r)
    {I : Type*} (D : CountableComponentModel r I) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ k : ℕ, ∀ f : Fin k → I, Function.Injective f → ∀ c,
      (∀ i j, D.label c (f i) = D.label c (f j)) →
      Lifting.entropyRoot (D.mass ∘ f) (fun i j => D.density c (f i) (f j)) ≤
        ENNReal.ofReal B) :
    beta r ≤ B := by
  have hp1 := density_lt_one_of_entropy_bounds D henergy
  let E : CountableComponentData r I := {
    mass := D.mass
    mass_pos := D.mass_pos
    mass_sum := D.mass_sum
    label := D.label
    density := D.density
    density_nonneg := D.density_nonneg
    density_lt_one := hp1
    density_symm := D.density_symm
    density_sum := D.density_sum
    density_zero := D.density_zero }
  apply beta_le_of_same_label_energy_bounds hr E hB
  intro k f hf c hlabel
  have hb := henergy k f hf c hlabel
  rw [entropyRoot_eq_of_lt_one (D.mass ∘ f) (fun i j => D.density c (f i) (f j))
    (fun i => (D.mass_pos (f i)).le) (fun i j => D.density_nonneg c (f i) (f j))
    (fun i j => hp1 c (f i) (f j))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

/-- A convenient form of countable component optimization: each finite
family carries an explicit common label. -/
theorem beta_le_of_labeled_extended_component_bounds {r : ℕ} (hr : 2 ≤ r)
    {I : Type*} (D : CountableComponentModel r I) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ k : ℕ, ∀ f : Fin k → I, Function.Injective f → ∀ c t,
      (∀ i, D.label c (f i) = t) →
      Lifting.entropyRoot (D.mass ∘ f) (fun i j => D.density c (f i) (f j)) ≤
        ENNReal.ofReal B) :
    beta r ≤ B := by
  apply beta_le_of_extended_component_bounds hr D hB
  intro k f hf c hlabels
  by_cases hk : k = 0
  · subst k
    simp only [Lifting.entropyRoot, Lifting.extendedEnergy, Finset.univ_eq_empty,
      Finset.sum_empty]
    simp
  · let i₀ : Fin k := ⟨0, by omega⟩
    exact henergy k f hf c (D.label c (f i₀)) (fun i => hlabels i i₀)

end HadwigerRamsey4Col.Transfer
