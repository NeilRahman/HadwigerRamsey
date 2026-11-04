import HadwigerRamsey.TwoBigSets.Finite

open scoped Classical BigOperators
open Finset
namespace HadwigerRamsey.Main

/-- Keep a prescribed number of elements without decreasing their average weight. -/
theorem exists_subset_average {V : Type*} [DecidableEq V]
    (S : Finset V) (f : V → ℝ) (m : ℕ) (hm : m ≤ S.card) :
    ∃ T ⊆ S, T.card = m ∧
      (m : ℝ) * (∑ v ∈ S, f v) ≤ (S.card : ℝ) * (∑ v ∈ T, f v) := by
  classical
  revert hm
  refine Finset.strongInductionOn S ?_
  intro S ih hm
  by_cases hm0 : m = 0
  · subst m
    exact ⟨∅,empty_subset _,by simp,by simp⟩
  by_cases he : m = S.card
  · exact ⟨S,Subset.rfl,he.symm,by simp [he]⟩
  have hmc : m < S.card := lt_of_le_of_ne hm he
  have hnon : S.Nonempty := card_pos.mp (by omega)
  have hsum : (∑ v ∈ S, (S.card : ℝ)*f v) ≤
      ∑ _v ∈ S, (∑ w ∈ S, f w) := by simp [mul_sum]
  obtain ⟨v,hv,hlow⟩ := exists_le_of_sum_le hnon hsum
  have hm' : m ≤ (S.erase v).card := by rw [card_erase_of_mem hv]; omega
  obtain ⟨T,hTS,hTm,havg⟩ := ih (S.erase v) (erase_ssubset hv) hm'
  refine ⟨T,hTS.trans (erase_subset _ _),hTm,?_⟩
  have hc : ((S.erase v).card : ℝ) = (S.card : ℝ)-1 := by
    rw [card_erase_of_mem hv,Nat.cast_sub (by omega : 1 ≤ S.card),Nat.cast_one]
  have hs : (∑ w ∈ S.erase v, f w) = (∑ w ∈ S, f w)-f v := by
    have hh := sum_erase_add S f hv
    linarith
  rw [hc,hs] at havg
  have hpos : 0 < (S.card : ℝ)-1 := by
    have hh : 1 < S.card := by omega
    have hhR : (1 : ℝ) < S.card := by exact_mod_cast hh
    linarith
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith only [mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg S.card),
    mul_le_mul_of_nonneg_left hlow hmR,hpos]

/-- Trim the second side of a bipartite cut to a specified size, preserving density. -/
theorem trim_cross_right {n m : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hm : m ≤ B.card) :
    ∃ B' ⊆ B, B'.card = m ∧
      (m : ℝ)*((G.interedges A B).card : ℝ) ≤
        (B.card : ℝ)*((G.interedges A B').card : ℝ) := by
  classical
  obtain ⟨B',hB',hcard,hs⟩ := exists_subset_average B
    (fun v => ((ControlledPartition.nbr G A v).card : ℝ)) m hm
  refine ⟨B',hB',hcard,?_⟩
  letI : Std.Symm G.Adj := G.symm
  have hcomm := Rel.card_interedges_comm (r := G.Adj) A B
  have hcomm' := Rel.card_interedges_comm (r := G.Adj) A B'
  change (G.interedges A B).card = (G.interedges B A).card at hcomm
  change (G.interedges A B').card = (G.interedges B' A).card at hcomm'
  rw [hcomm,hcomm',TwoBigSets.interedges_card_sum,TwoBigSets.interedges_card_sum,
    Nat.cast_sum,Nat.cast_sum]
  exact hs

/-- Equal-size subsets preserve any lower bound on the crossing edge density. -/
theorem balanced_dense_subsets {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) {d : ℝ} (hA : 0 < A.card) (hB : 0 < B.card)
    (hdensity : d*(A.card : ℝ)*B.card ≤ (G.interedges A B).card) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, A'.card = min A.card B.card ∧
      B'.card = min A.card B.card ∧
      d*(A'.card : ℝ)^2 ≤ (G.interedges A' B').card := by
  classical
  by_cases hAB : A.card ≤ B.card
  · obtain ⟨B',hB',hcard,havg⟩ := trim_cross_right G A B hAB
    refine ⟨A,Subset.rfl,B',hB',by simp [min_eq_left hAB],?_,?_⟩
    · simpa only [min_eq_left hAB] using hcard
    · have hpos : (0 : ℝ) < B.card := by exact_mod_cast hB
      have hh := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg A.card)
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith only [hh,havg]
  · have hBA : B.card ≤ A.card := (le_of_not_ge hAB)
    have hD : d*(B.card : ℝ)*A.card ≤ (G.interedges B A).card := by
      letI : Std.Symm G.Adj := G.symm
      have hh := Rel.card_interedges_comm (r := G.Adj) A B
      change (G.interedges A B).card = (G.interedges B A).card at hh
      rw [←hh]
      nlinarith only [hdensity]
    obtain ⟨A',hA',hcard,havg⟩ := trim_cross_right G B A hBA
    refine ⟨A',hA',B,Subset.rfl,?_,by simp [min_eq_right hBA],?_⟩
    · simpa only [min_eq_right hBA] using hcard
    · have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA
      have hh := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg B.card)
      letI : Std.Symm G.Adj := G.symm
      have hcomm := Rel.card_interedges_comm (r := G.Adj) A' B
      change (G.interedges A' B).card = (G.interedges B A').card at hcomm
      rw [hcomm,hcard]
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith only [hh,havg]

end HadwigerRamsey.Main
