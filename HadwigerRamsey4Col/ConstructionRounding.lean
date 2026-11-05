import Mathlib

open scoped BigOperators Topology Classical
open Filter

namespace HadwigerRamsey4Col
namespace Construction

/-- Flooring each mass leaves a nonnegative integer remainder. -/
lemma sum_floor_le {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : ∑ i, a i = 1) (n : ℕ) : ∑ i, ⌊a i * n⌋₊ ≤ n := by
  have h : (∑ i, (⌊a i * n⌋₊ : ℝ)) ≤ n := by
    calc
      _ ≤ ∑ i, a i * n := Finset.sum_le_sum (fun i _ => Nat.floor_le (mul_nonneg (ha i) (Nat.cast_nonneg n)))
      _ = n := by rw [← Finset.sum_mul, hs, one_mul]
  exact_mod_cast h

/-- Give the entire floor-rounding remainder to one distinguished part. -/
noncomputable def roundedCount {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    (n : ℕ) (i : Fin k) : ℕ :=
  ⌊a i * n⌋₊ + if i = ⟨0, hk⟩ then n - ∑ j, ⌊a j * n⌋₊ else 0

lemma sum_roundedCount {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (n : ℕ) :
    ∑ i, roundedCount hk a n i = n := by
  simp only [roundedCount, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Nat.add_sub_of_le (sum_floor_le a ha hs n)

lemma roundedCount_ratio {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (i : Fin k) :
    Tendsto (fun n : ℕ => (roundedCount hk a n i : ℝ) / n) atTop (𝓝 (a i)) := by
  have hf (j : Fin k) :
      Tendsto (fun n : ℕ => (⌊a j * n⌋₊ : ℝ) / n) atTop (𝓝 (a j)) :=
    (tendsto_nat_floor_mul_div_atTop (ha j)).comp tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ => (∑ j, (⌊a j * n⌋₊ : ℝ)) / n)
      atTop (𝓝 1) := by
    simpa only [Finset.sum_div, hs] using tendsto_finsetSum Finset.univ (fun j _ => hf j)
  have hrem : Tendsto (fun n : ℕ => ((n - ∑ j, ⌊a j * n⌋₊ : ℕ) : ℝ) / n)
      atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 1 - (∑ j, (⌊a j * n⌋₊ : ℝ)) / n)
        atTop (𝓝 0) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsum
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.cast_sub (sum_floor_le a ha hs n), Nat.cast_sum, sub_div]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [div_self hn0]
  by_cases hi : i = ⟨0, hk⟩
  · simpa only [roundedCount, if_pos hi, Nat.cast_add, add_div, add_zero] using (hf i).add hrem
  · simpa only [roundedCount, if_neg hi, add_zero] using hf i

/-- An exact realization of arbitrary integer part sizes by a vertex partition. -/
lemma exists_partition_of_counts {k n : ℕ} (m : Fin k → ℕ) (hs : ∑ i, m i = n) :
    ∃ τ : Fin n → Fin k, ∀ i, (Finset.univ.filter (fun v => τ v = i)).card = m i := by
  let e : (Σ i : Fin k, Fin (m i)) ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hs)
  let τ : Fin n → Fin k := fun v => (e.symm v).1
  refine ⟨τ, fun i => ?_⟩
  let f : Fin (m i) → {v : Fin n // τ v = i} :=
    fun v => ⟨e ⟨i, v⟩, by simp [τ]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h' : e ⟨i, v⟩ = e ⟨i, w⟩ := congrArg Subtype.val h
      exact eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h')).2
    · intro v
      obtain ⟨j, w, hjw⟩ := Sigma.exists.mp (show ∃ z, e z = v.val from ⟨e.symm v.val, by simp⟩)
      have hj : j = i := by
        have := v.property
        dsimp [τ] at this
        rw [← hjw, Equiv.symm_apply_apply] at this
        exact this
      subst j
      exact ⟨w, Subtype.ext hjw⟩
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_fin, Fintype.card_subtype] using hh.symm

/-- Every positive real mass vector is realized by partitions at every order,
with relative part sizes converging to the prescribed masses. -/
theorem exists_convergent_partitions {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) :
    ∃ τ : ∀ n : ℕ, Fin n → Fin k, ∀ i,
      Tendsto (fun n : ℕ =>
        ((Finset.univ.filter (fun v => τ n v = i)).card : ℝ) / n) atTop (𝓝 (a i)) := by
  choose τ hτ using fun n => exists_partition_of_counts (roundedCount hk a n)
    (sum_roundedCount hk a ha hs n)
  refine ⟨τ, fun i => ?_⟩
  simp_rw [hτ]
  exact roundedCount_ratio hk a ha hs i

end Construction
end HadwigerRamsey4Col
