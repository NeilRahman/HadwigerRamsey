import Mathlib

open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A finite greedy allocation of small, disjoint sets from a reservoir.
The local choice condition allows all vertices allocated at earlier steps
to be excluded. It is used for both domination and path allocation. -/
theorem disjoint_reservoir_selection {I V : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq V] (D : Finset V) (L : ℕ)
    (P : I → Finset V → Prop)
    (hchoose : ∀ i, ∀ U ⊆ D, U.card ≤ Fintype.card I * L →
      ∃ M ⊆ D \ U, M.card ≤ L ∧ P i M) :
    ∃ M : I → Finset V, (∀ i, M i ⊆ D ∧ (M i).card ≤ L ∧ P i (M i)) ∧
      ∀ i j, i ≠ j → Disjoint (M i) (M j) := by
  have hfinite : ∀ S : Finset I,
      ∃ M : I → Finset V,
        (∀ i ∈ S, M i ⊆ D ∧ (M i).card ≤ L ∧ P i (M i)) ∧
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (M i) (M j)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => ∅, by simp, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨M, hM, hd⟩ := ih
      let U := S.biUnion M
      have hUD : U ⊆ D := by
        intro v hv
        obtain ⟨j, hj, hv⟩ := mem_biUnion.mp hv
        exact (hM j hj).1 hv
      have hcard : U.card ≤ Fintype.card I * L := by
        calc
          _ ≤ ∑ j ∈ S, (M j).card := card_biUnion_le
          _ ≤ ∑ _j ∈ S, L := sum_le_sum fun j hj => (hM j hj).2.1
          _ = S.card * L := by simp
          _ ≤ Fintype.card I * L := Nat.mul_le_mul_right _ (card_le_univ S)
      obtain ⟨N, hN, hNL, hNP⟩ := hchoose i U hUD hcard
      let M' := Function.update M i N
      have hnew : M' i = N := by simp [M']
      have hold : ∀ j ∈ S, M' j = M j := by
        intro j hj
        have hji : j ≠ i := by intro hji; subst j; exact hi hj
        exact Function.update_of_ne hji _ _
      refine ⟨M', ?_, ?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · rw [hnew]
          exact ⟨hN.trans sdiff_subset, hNL, hNP⟩
        · rw [hold j hj]
          exact hM j hj
      · have hNj : ∀ j ∈ S, Disjoint N (M j) := by
          intro j hj
          apply Finset.disjoint_left.mpr
          intro v hvN hvj
          exact (mem_sdiff.mp (hN hvN)).2 (mem_biUnion.mpr ⟨j, hj, hvj⟩)
        intro j hj k hk hjk
        by_cases hji : j = i
        · subst j
          have hki : k ≠ i := Ne.symm hjk
          have hkS : k ∈ S := (mem_insert.mp hk).resolve_left hki
          rw [hnew, hold k hkS]; exact hNj k hkS
        · have hjS : j ∈ S := (mem_insert.mp hj).resolve_left hji
          by_cases hki : k = i
          · subst k
            rw [hold j hjS, hnew]; exact (hNj j hjS).symm
          · have hkS : k ∈ S := (mem_insert.mp hk).resolve_left hki
            rw [hold j hjS, hold k hkS]; exact hd j hjS k hkS hjk
  obtain ⟨M, hM, hd⟩ := hfinite univ
  exact ⟨M, fun i => hM i (mem_univ _), fun i j hij => hd i (mem_univ _) j (mem_univ _) hij⟩

end HadwigerRamsey.ThomasonUpper
