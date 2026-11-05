import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace ComponentTransfer

/-- A finite component instance. A label map describes each colour's partition;
unused labels contribute empty parts and therefore zero energy. -/
structure ComponentInstance (r : ℕ) where
  k : ℕ
  k_pos : 0 < k
  mass : Fin k → ℝ
  mass_pos : ∀ i, 0 < mass i
  mass_sum : ∑ i, mass i = 1
  label : Fin r → Fin k → Fin k
  density : Fin r → Fin k → Fin k → ℝ
  density_nonneg : ∀ c i j, 0 ≤ density c i j
  density_lt_one : ∀ c i j, density c i j < 1
  density_symm : ∀ c i j, density c i j = density c j i
  density_sum : ∀ i j, ∑ c, density c i j = 1
  density_zero : ∀ c i j, label c i ≠ label c j → density c i j = 0

namespace ComponentInstance

variable {r : ℕ} (I : ComponentInstance r)

noncomputable def partMass (c : Fin r) (t : Fin I.k) : ℝ :=
  ∑ i with I.label c i = t, I.mass i

noncomputable def partDensity (c : Fin r) (t : Fin I.k) : ℝ :=
  ∑ i with I.label c i = t, ∑ j with I.label c j = t,
    I.mass i * I.mass j * I.density c i j

noncomputable def partEntropy (c : Fin r) (t : Fin I.k) : ℝ :=
  ∑ i with I.label c i = t, ∑ j with I.label c j = t,
    I.mass i * I.mass j * (-Real.log (1 - I.density c i j))

noncomputable def energy (c : Fin r) (t : Fin I.k) : ℝ :=
  Real.sqrt (I.partEntropy c t)

/-- The maximum in the finite component optimization problem. -/
noncomputable def objective : ℝ :=
  sSup (Set.range (fun a : Fin r × Fin I.k => I.energy a.1 a.2))

theorem energy_le_objective (c : Fin r) (t : Fin I.k) :
    I.energy c t ≤ I.objective :=
  le_csSup (Set.finite_range _).bddAbove ⟨(c,t), rfl⟩

theorem partMass_nonneg (c : Fin r) (t : Fin I.k) : 0 ≤ I.partMass c t :=
  Finset.sum_nonneg (fun i _ => (I.mass_pos i).le)

theorem partDensity_nonneg (c : Fin r) (t : Fin I.k) : 0 ≤ I.partDensity c t :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (I.mass_pos i).le (I.mass_pos j).le) (I.density_nonneg c i j)))

theorem density_le_entropy (c : Fin r) (t : Fin I.k) :
    I.partDensity c t ≤ I.partEntropy c t := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (I.mass_pos i).le (I.mass_pos j).le)
  have := Real.log_le_sub_one_of_pos (sub_pos.mpr (I.density_lt_one c i j))
  linarith

theorem partEntropy_nonneg (c : Fin r) (t : Fin I.k) : 0 ≤ I.partEntropy c t :=
  (I.partDensity_nonneg c t).trans (I.density_le_entropy c t)

/-- Vanishing component entropy forces all within-component densities to vanish. -/
theorem density_zero_of_partEntropy_zero (c : Fin r) (t : Fin I.k)
    (hE : I.partEntropy c t = 0) (i j : Fin I.k)
    (hi : I.label c i = t) (hj : I.label c j = t) : I.density c i j = 0 := by
  have hD : I.partDensity c t = 0 := by
    have := I.density_le_entropy c t
    have := I.partDensity_nonneg c t
    linarith
  have hn : ∀ i j : Fin I.k, 0 ≤ I.mass i * I.mass j * I.density c i j :=
    fun i j => mul_nonneg (mul_nonneg (I.mass_pos i).le (I.mass_pos j).le)
      (I.density_nonneg c i j)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hn i j))).mp hD i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp hrow j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  exact (mul_eq_zero.mp hij).resolve_left
    (mul_ne_zero (ne_of_gt (I.mass_pos i)) (ne_of_gt (I.mass_pos j)))

theorem density_zero_of_energy_zero (c : Fin r) (t : Fin I.k)
    (hE : I.energy c t = 0) (i j : Fin I.k)
    (hi : I.label c i = t) (hj : I.label c j = t) : I.density c i j = 0 := by
  apply I.density_zero_of_partEntropy_zero c t _ i j hi hj
  have hsq := Real.sq_sqrt (I.partEntropy_nonneg c t)
  change I.energy c t ^ 2 = I.partEntropy c t at hsq
  rw [hE] at hsq
  simpa using hsq.symm

theorem partDensity_le_mass_sq (c : Fin r) (t : Fin I.k) :
    I.partDensity c t ≤ I.partMass c t ^ 2 := by
  unfold partDensity partMass
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_of_le_one_right (mul_nonneg (I.mass_pos i).le (I.mass_pos j).le)
    (I.density_lt_one c i j).le

theorem partDensity_le_objective_mass (c : Fin r) (t : Fin I.k) :
    I.partDensity c t ≤ I.objective * I.partMass c t := by
  have hd := I.partDensity_nonneg c t
  have hs := I.partMass_nonneg c t
  have he := I.partEntropy_nonneg c t
  have hE := I.energy_le_objective c t
  have hsqrt := Real.sq_sqrt he
  have hEn := Real.sqrt_nonneg (I.partEntropy c t)
  have hde := I.density_le_entropy c t
  have hds := I.partDensity_le_mass_sq c t
  change Real.sqrt (I.partEntropy c t) ≤ I.objective at hE
  have hm : 0 ≤ I.objective := hEn.trans hE
  by_cases h : I.objective ≤ I.partMass c t
  · have hsq : I.partDensity c t ≤ I.objective ^ 2 := by nlinarith
    nlinarith
  · have h : I.partMass c t ≤ I.objective := (le_of_not_ge h)
    nlinarith

theorem sum_partMass (c : Fin r) : ∑ t, I.partMass c t = 1 := by
  classical
  simp only [partMass, Finset.sum_filter]
  rw [Finset.sum_comm]
  simpa using I.mass_sum

theorem sum_partDensity (c : Fin r) :
    ∑ t, I.partDensity c t = ∑ i, ∑ j, I.mass i * I.mass j * I.density c i j := by
  classical
  simp only [partDensity, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h
  · rfl
  · rw [I.density_zero c i j (Ne.symm h), mul_zero]

theorem sum_all_partDensity : ∑ c, ∑ t, I.partDensity c t = 1 := by
  simp_rw [I.sum_partDensity]
  rw [Finset.sum_comm]
  trans ∑ i, ∑ j, I.mass i * I.mass j
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum, I.density_sum, mul_one]
  · rw [← Finset.sum_mul_sum, I.mass_sum, one_mul]

theorem inv_colors_le_objective (hr : 2 ≤ r) : (r : ℝ)⁻¹ ≤ I.objective := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have h := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
    Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => I.partDensity_le_objective_mass c t))
  rw [I.sum_all_partDensity] at h
  simp only [← Finset.mul_sum, I.sum_partMass, mul_one] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hrpos).2
  nlinarith

/-- The one-part equal-density instance witnesses nonemptiness. -/
noncomputable def uniform (r : ℕ) (hr : 2 ≤ r) : ComponentInstance r where
  k := 1
  k_pos := by decide
  mass := fun _ => 1
  mass_pos := by simp
  mass_sum := by simp
  label := fun _ _ => 0
  density := fun _ _ _ => (r : ℝ)⁻¹
  density_nonneg := by intros; positivity
  density_lt_one := by
    intros
    apply (inv_lt_one₀ (by exact_mod_cast (by omega : 0 < r))).2
    exact_mod_cast (by omega : 1 < r)
  density_symm := by intros; rfl
  density_sum := by
    intros
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (by omega : r ≠ 0))
  density_zero := by intros c i j h; exact (h rfl).elim

end ComponentInstance

/-- The infimum over all finite component instances, as in equation (1). -/
noncomputable def beta (r : ℕ) : ℝ :=
  sInf (Set.range (fun I : ComponentInstance r => I.objective))


theorem beta_le_objective {r : ℕ} (hr : 2 ≤ r) (I : ComponentInstance r) :
    beta r ≤ I.objective := by
  apply csInf_le
  · exact ⟨(r : ℝ)⁻¹, by rintro _ ⟨J, rfl⟩; exact J.inv_colors_le_objective hr⟩
  · exact ⟨I, rfl⟩

theorem inv_colors_le_beta {r : ℕ} (hr : 2 ≤ r) : (r : ℝ)⁻¹ ≤ beta r := by
  apply le_csInf
  · exact ⟨(ComponentInstance.uniform r hr).objective, ⟨ComponentInstance.uniform r hr, rfl⟩⟩
  · rintro _ ⟨I, rfl⟩
    exact I.inv_colors_le_objective hr

theorem beta_pos {r : ℕ} (hr : 2 ≤ r) : 0 < beta r :=
  (inv_pos.mpr (by exact_mod_cast (by omega : 0 < r))).trans_le (inv_colors_le_beta hr)

/-- Every positive accuracy admits a finite instance within that accuracy. -/
theorem exists_objective_lt {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ I : ComponentInstance r, I.objective < beta r + ε := by
  have hn : (Set.range (fun I : ComponentInstance r => I.objective)).Nonempty :=
    ⟨_, ⟨ComponentInstance.uniform r hr, rfl⟩⟩
  obtain ⟨v, ⟨I, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hn
    (show beta r < beta r + ε by linarith)
  exact ⟨I, hv⟩

/-- Some colour component attains at least the infimum energy. -/
theorem exists_energy_ge_beta {r : ℕ} (hr : 2 ≤ r) (I : ComponentInstance r) :
    ∃ c t, beta r ≤ I.energy c t := by
  have hn : (Set.range (fun a : Fin r × Fin I.k => I.energy a.1 a.2)).Nonempty :=
    ⟨_, ⟨(⟨0, by omega⟩, ⟨0, I.k_pos⟩), rfl⟩⟩
  obtain ⟨⟨c,t⟩, ht⟩ := hn.csSup_mem (Set.finite_range _)
  refine ⟨c, t, ?_⟩
  calc beta r ≤ I.objective := beta_le_objective hr I
       _ = I.energy c t := ht.symm

end ComponentTransfer
