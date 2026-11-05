import ComponentTransfer.ComponentProgram
import ComponentTransfer.LiftingEntropy

open scoped BigOperators Classical Topology
open Filter Finset Real

set_option backward.isDefEq.respectTransparency false

namespace ComponentTransfer.Transfer

/-- Compress the labels occurring in a finite family, preserving exactly
which pairs receive the same label. -/
noncomputable def finiteLabel {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : Fin k :=
  (Finset.univ.filter (fun j => f j = f i)).min' ⟨i, by simp⟩

lemma finiteLabel_value {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    f (finiteLabel f i) = f i := by
  unfold finiteLabel
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun j => f j = f i)) _)).2

lemma finiteLabel_eq_iff {k : ℕ} (f : Fin k → ℕ) (i j : Fin k) :
    finiteLabel f i = finiteLabel f j ↔ f i = f j := by
  constructor
  · intro h
    exact (finiteLabel_value f i).symm.trans ((congrArg f h).trans (finiteLabel_value f j))
  · intro h
    simp only [finiteLabel, h]

lemma finiteLabel_idempotent {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    finiteLabel f (finiteLabel f i) = finiteLabel f i :=
  (finiteLabel_eq_iff f _ _).mpr (finiteLabel_value f i)

/-- The finite normalization of countable component data. -/
noncomputable def normalizedInstance {r k : ℕ} (hk : 0 < k)
    (u : Fin k → ℝ) (hu : ∀ i, 0 < u i)
    (label : Fin r → Fin k → ℕ) (p : Fin r → Fin k → Fin k → ℝ)
    (hp0 : ∀ c i j, 0 ≤ p c i j) (hp1 : ∀ c i j, p c i j < 1)
    (hpsymm : ∀ c i j, p c i j = p c j i)
    (hpsum : ∀ i j, ∑ c, p c i j = 1)
    (hpzero : ∀ c i j, label c i ≠ label c j → p c i j = 0) :
    ComponentInstance r where
  k := k
  k_pos := hk
  mass := fun i => u i / ∑ j, u j
  mass_pos := fun i => div_pos (hu i) (Finset.sum_pos (fun j _ => hu j) ⟨⟨0,hk⟩, Finset.mem_univ _⟩)
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos (fun j _ => hu j) ⟨⟨0,hk⟩, Finset.mem_univ _⟩))
  label := fun c => finiteLabel (label c)
  density := p
  density_nonneg := hp0
  density_lt_one := hp1
  density_symm := hpsymm
  density_sum := hpsum
  density_zero := by
    intro c i j hij
    apply hpzero c i j
    exact fun h => hij ((finiteLabel_eq_iff _ _ _).mpr h)

/-- A finite label-class entropy, before the total retained mass is
normalized to one. -/
noncomputable def finitePartEntropy {r k : ℕ} (u : Fin k → ℝ)
    (label : Fin r → Fin k → ℕ) (p : Fin r → Fin k → Fin k → ℝ)
    (c : Fin r) (t : ℕ) : ℝ :=
  ∑ i with label c i = t, ∑ j with label c j = t,
    u i*u j*(-log (1-p c i j))

lemma normalizedInstance_partEntropy {r k : ℕ} (hk : 0 < k)
    (u : Fin k → ℝ) (hu : ∀ i, 0 < u i)
    (label : Fin r → Fin k → ℕ) (p : Fin r → Fin k → Fin k → ℝ)
    (hp0 : ∀ c i j, 0 ≤ p c i j) (hp1 : ∀ c i j, p c i j < 1)
    (hpsymm : ∀ c i j, p c i j = p c j i)
    (hpsum : ∀ i j, ∑ c, p c i j = 1)
    (hpzero : ∀ c i j, label c i ≠ label c j → p c i j = 0)
    (c : Fin r) (t : Fin k) (hfix : finiteLabel (label c) t = t) :
    (normalizedInstance hk u hu label p hp0 hp1 hpsymm hpsum hpzero).partEntropy c t =
      finitePartEntropy u label p c (label c t) / (∑ i, u i)^2 := by
  unfold ComponentInstance.partEntropy finitePartEntropy
  simp only [normalizedInstance]
  have hpred (i : Fin k) : finiteLabel (label c) i = t ↔ label c i = label c t := by
    simpa only [hfix] using finiteLabel_eq_iff (label c) i t
  simp_rw [hpred, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Normalizing retained atoms costs exactly the reciprocal of their total
mass in the component objective. -/
theorem beta_mul_sum_le_of_finite_bounds {r k : ℕ} (hr : 2 ≤ r) (hk : 0 < k)
    (u : Fin k → ℝ) (hu : ∀ i, 0 < u i)
    (label : Fin r → Fin k → ℕ) (p : Fin r → Fin k → Fin k → ℝ)
    (hp0 : ∀ c i j, 0 ≤ p c i j) (hp1 : ∀ c i j, p c i j < 1)
    (hpsymm : ∀ c i j, p c i j = p c j i)
    (hpsum : ∀ i j, ∑ c, p c i j = 1)
    (hpzero : ∀ c i j, label c i ≠ label c j → p c i j = 0)
    {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ c t, sqrt (finitePartEntropy u label p c t) ≤ B) :
    beta r * ∑ i, u i ≤ B := by
  let J := normalizedInstance hk u hu label p hp0 hp1 hpsymm hpsum hpzero
  let s : ℝ := ∑ i, u i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hu i) ⟨⟨0,hk⟩, Finset.mem_univ _⟩
  have hpart (c : Fin r) (t : Fin k) : J.energy c t ≤ B/s := by
    by_cases hfix : finiteLabel (label c) t = t
    swap
    · have hempty : (Finset.univ.filter (fun i => finiteLabel (label c) i = t)) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hi
        apply hfix
        rw [← hi]
        exact finiteLabel_idempotent (label c) i
      have hz : J.energy c t = 0 := by
        unfold ComponentInstance.energy ComponentInstance.partEntropy
        change sqrt (∑ i : Fin k with finiteLabel (label c) i = t,
          ∑ j : Fin k with finiteLabel (label c) j = t,
            (u i / ∑ j, u j)*(u j / ∑ j, u j)*(-log (1-p c i j))) = 0
        rw [hempty, Finset.sum_empty, Real.sqrt_zero]
      rw [hz]
      exact div_nonneg hB hs.le
    have he : J.partEntropy c t = finitePartEntropy u label p c (label c t)/s^2 :=
      normalizedInstance_partEntropy hk u hu label p hp0 hp1 hpsymm hpsum hpzero c t hfix
    have hroot := Real.sq_sqrt (J.partEntropy_nonneg c t)
    have hdiv : J.partEntropy c t*s^2 = finitePartEntropy u label p c (label c t) := by
      rw [he]
      exact div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hs))
    have hnon : 0 ≤ finitePartEntropy u label p c (label c t) := by
      rw [← hdiv]
      exact mul_nonneg (J.partEntropy_nonneg c t) (sq_nonneg s)
    have hraw := Real.sq_sqrt hnon
    have hb := henergy c (label c t)
    have hj : 0 ≤ J.energy c t := Real.sqrt_nonneg _
    have hraw0 := Real.sqrt_nonneg (finitePartEntropy u label p c (label c t))
    change J.energy c t ^ 2 = J.partEntropy c t at hroot
    apply (le_div_iff₀ hs).mpr
    nlinarith [sq_nonneg (J.energy c t * s - B)]
  have hobj : J.objective ≤ B/s := by
    apply csSup_le
    · exact ⟨J.energy ⟨0,by omega⟩ ⟨0,hk⟩, ⟨(⟨0,by omega⟩,⟨0,hk⟩),rfl⟩⟩
    · rintro _ ⟨⟨c,t⟩,rfl⟩
      exact hpart c t
  have hb := (beta_le_objective hr J).trans hobj
  exact (le_div_iff₀ hs).mp hb

/-- Countably many positive component atoms. The finite-energy premise is
stated after selecting and enumerating finitely many atoms, so it can be
supplied directly by the entropy lifting theorem. -/
structure CountableComponentData (r : ℕ) (I : Type*) where
  mass : I → ℝ
  mass_pos : ∀ i, 0 < mass i
  mass_sum : HasSum mass 1
  label : Fin r → I → ℕ
  density : Fin r → I → I → ℝ
  density_nonneg : ∀ c i j, 0 ≤ density c i j
  density_lt_one : ∀ c i j, density c i j < 1
  density_symm : ∀ c i j, density c i j = density c j i
  density_sum : ∀ i j, ∑ c, density c i j = 1
  density_zero : ∀ c i j, label c i ≠ label c j → density c i j = 0

/-- The finite component infimum also bounds any countable component data
whose finite label-class entropy roots are uniformly at most `B`. -/
theorem beta_le_of_countable_component_data {r : ℕ} (hr : 2 ≤ r)
    {I : Type*} (D : CountableComponentData r I) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ k : ℕ, ∀ f : Fin k → I, Function.Injective f → ∀ c t,
      sqrt (finitePartEntropy (D.mass ∘ f) (fun c => D.label c ∘ f)
        (fun c i j => D.density c (f i) (f j)) c t) ≤ B) :
    beta r ≤ B := by
  classical
  by_contra hnot
  have hBbeta : B < beta r := lt_of_not_ge hnot
  have hlim : Tendsto (fun s : Finset I => beta r * ∑ i ∈ s, D.mass i) atTop
      (𝓝 (beta r)) := by
    have hm : Tendsto (fun s : Finset I => ∑ i ∈ s, D.mass i) atTop (𝓝 (1 : ℝ)) := D.mass_sum
    simpa using hm.const_mul (beta r)
  have hevent : ∀ᶠ s : Finset I in atTop, B < beta r*∑ i ∈ s, D.mass i :=
    (tendsto_order.mp hlim).1 B hBbeta
  obtain ⟨s,hs⟩ := hevent.exists
  have hsum : 0 < ∑ i ∈ s, D.mass i := by
    have hbp := beta_pos hr
    nlinarith
  have hsne : s.Nonempty := Finset.nonempty_of_sum_ne_zero (ne_of_gt hsum)
  let f : Fin s.card → I := fun i => (s.equivFin.symm i).val
  have hf : Function.Injective f := Subtype.val_injective.comp s.equivFin.symm.injective
  have hsumEq : ∑ i : Fin s.card, D.mass (f i) = ∑ i ∈ s, D.mass i := by
    exact (Fintype.sum_equiv s.equivFin.symm (fun i => D.mass (f i))
      (fun i : s => D.mass i) (fun i => rfl)).trans (Finset.sum_coe_sort s D.mass)
  have hfinite := beta_mul_sum_le_of_finite_bounds hr hsne.card_pos
    (D.mass ∘ f) (fun i => D.mass_pos (f i)) (fun c => D.label c ∘ f)
    (fun c i j => D.density c (f i) (f j))
    (fun c i j => D.density_nonneg c (f i) (f j))
    (fun c i j => D.density_lt_one c (f i) (f j))
    (fun c i j => D.density_symm c (f i) (f j))
    (fun i j => D.density_sum (f i) (f j))
    (fun c i j h => D.density_zero c (f i) (f j) h) hB
    (henergy s.card f hf)
  simp only [Function.comp_apply] at hfinite
  rw [hsumEq] at hfinite
  linarith

lemma sum_finset_enumeration {I : Type*} (s : Finset I) (f : I → ℝ) :
    (∑ i : Fin s.card, f (s.equivFin.symm i).val) = ∑ i ∈ s, f i := by
  exact (Fintype.sum_equiv s.equivFin.symm _ _ (fun i => rfl)).trans
    (Finset.sum_coe_sort s f)

lemma finitePartEntropy_eq_enumeration {r k : ℕ} (u : Fin k → ℝ)
    (label : Fin r → Fin k → ℕ) (p : Fin r → Fin k → Fin k → ℝ)
    (c : Fin r) (t : ℕ) :
    let s := Finset.univ.filter (fun i => label c i = t)
    finitePartEntropy u label p c t =
      ∑ i : Fin s.card, ∑ j : Fin s.card,
        u (s.equivFin.symm i).val*u (s.equivFin.symm j).val*
          (-log (1-p c (s.equivFin.symm i).val (s.equivFin.symm j).val)) := by
  dsimp only
  unfold finitePartEntropy
  rw [← sum_finset_enumeration]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sum_finset_enumeration]

/-- It suffices to bound finite families which all lie in one label class. -/
theorem beta_le_of_same_label_energy_bounds {r : ℕ} (hr : 2 ≤ r)
    {I : Type*} (D : CountableComponentData r I) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ k : ℕ, ∀ f : Fin k → I, Function.Injective f → ∀ c,
      (∀ i j, D.label c (f i) = D.label c (f j)) →
      sqrt (∑ i, ∑ j, D.mass (f i)*D.mass (f j)*
        (-log (1-D.density c (f i) (f j)))) ≤ B) :
    beta r ≤ B := by
  apply beta_le_of_countable_component_data hr D hB
  intro k f hf c t
  let s := Finset.univ.filter (fun i : Fin k => D.label c (f i) = t)
  let g : Fin s.card → I := fun i => f (s.equivFin.symm i).val
  have hg : Function.Injective g := hf.comp (Subtype.val_injective.comp s.equivFin.symm.injective)
  have hlabel (i j : Fin s.card) : D.label c (g i) = D.label c (g j) := by
    have hi := (Finset.mem_filter.mp (s.equivFin.symm i).property).2
    have hj := (Finset.mem_filter.mp (s.equivFin.symm j).property).2
    exact hi.trans hj.symm
  have hb := henergy s.card g hg c hlabel
  rw [finitePartEntropy_eq_enumeration]
  exact hb

end ComponentTransfer.Transfer
