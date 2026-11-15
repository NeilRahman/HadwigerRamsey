import HadwigerRamsey.Graph

open scoped BigOperators
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- The vertices of a simple path other than its two endpoints. -/
noncomputable def pathInterior {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (p : G.Path u v) : Finset (Fin n) :=
  p.val.support.toFinset \ {u, v}

theorem pathInterior_card {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (p : G.Path u v) :
    (pathInterior p).card + 1 = p.val.length := by
  classical
  have hsub : ({u, v} : Finset (Fin n)) ⊆ p.val.support.toFinset := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact List.mem_toFinset.mpr p.val.start_mem_support
    · rw [mem_singleton] at hx
      subst x
      exact List.mem_toFinset.mpr p.val.end_mem_support
  have hcard := card_sdiff_add_card_eq_card hsub
  have hpair : ({u, v} : Finset (Fin n)).card = 2 := by simp [huv]
  have hsupport : p.val.support.toFinset.card = p.val.length + 1 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup, SimpleGraph.Walk.length_support]
  change (pathInterior p).card + ({u, v} : Finset (Fin n)).card = _ at hcard
  omega

/-- The internal vertices of a disjoint family use at most the available
vertices. This is the short-path counting input within Lemma A.4. -/
theorem sum_pathInterior_card_le {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (P : Finset (G.Path u v))
    (hd : (P : Set (G.Path u v)).PairwiseDisjoint pathInterior) :
    ∑ p ∈ P, (pathInterior p).card ≤ n := by
  classical
  rw [← card_biUnion hd]
  simpa using card_le_univ (P.biUnion pathInterior)

/-- The short-path counting step in Lemma A.4, starting from any family of at
least k distinct internally vertex-disjoint paths supplied by Menger. -/
theorem short_paths_of_family {n k : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} (huv : u ≠ v) (hk : 0 < k)
    (P : Finset (G.Path u v)) (hkP : k ≤ P.card)
    (hd : (P : Set (G.Path u v)).PairwiseDisjoint pathInterior) :
    ∃ Q : Finset (G.Path u v), Q ⊆ P ∧ k ≤ 2 * Q.card ∧
      (∀ p ∈ Q, (p.val.length : ℝ) ≤ 2 * n / (k : ℝ) + 1) ∧
      (Q : Set (G.Path u v)).PairwiseDisjoint pathInterior := by
  classical
  let Q := P.filter fun p => (p.val.length : ℝ) ≤ 2 * n / (k : ℝ) + 1
  let B := P.filter fun p => ¬ (p.val.length : ℝ) ≤ 2 * n / (k : ℝ) + 1
  have hpart : Q.card + B.card = P.card := card_filter_add_card_filter_not _
  have hn : 0 < n := Fin.pos u
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hBbound : (B.card : ℝ) * (2 * n / (k : ℝ)) ≤ n := by
    calc
      _ = ∑ _p ∈ B, 2 * n / (k : ℝ) := by simp
      _ ≤ ∑ p ∈ B, ((pathInterior p).card : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpbad := (mem_filter.mp hp).2
        have hlen : ((pathInterior p).card : ℝ) + 1 = p.val.length := by
          exact_mod_cast pathInterior_card huv p
        push Not at hpbad
        linarith
      _ ≤ ∑ p ∈ P, ((pathInterior p).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ ≤ n := by exact_mod_cast sum_pathInterior_card_le P hd
  have hbad : 2 * B.card ≤ k := by
    have h := (div_le_iff₀ hkR).mp (by
      simpa [mul_div_assoc] using hBbound : (B.card : ℝ) * (2 * n) / k ≤ n)
    have h' : (2 : ℝ) * B.card ≤ k := by nlinarith
    exact_mod_cast h'
  refine ⟨Q, filter_subset _ _, by omega, ?_, ?_⟩
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro p hp q hq hpq
    exact hd (mem_filter.mp hp).1 (mem_filter.mp hq).1 hpq

end HadwigerRamsey.ThomasonUpper
