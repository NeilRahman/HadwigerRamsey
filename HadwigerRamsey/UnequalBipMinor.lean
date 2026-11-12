import HadwigerRamsey.Main.DensityCaps

open scoped Classical
open Finset Real

namespace HadwigerRamsey

/-- In a bipartite graph, counting crossing edges once counts every edge. -/
lemma bipartite_interedges_card {n : ℕ} (H : SimpleGraph (Fin n))
    (A B : Finset (Fin n))
    (h : H.IsBipartiteWith (A : Set (Fin n)) (B : Set (Fin n))) :
    (H.interedges A B).card = H.edgeFinset.card := by
  classical
  rw [TwoBigSets.interedges_card_sum]
  calc
    _ = ∑ v ∈ A, H.degree v := by
      apply sum_congr rfl
      intro v hv
      have hnbr : ControlledPartition.nbr H B v = H.neighborFinset v := by
        ext w
        simp only [ControlledPartition.nbr, mem_filter, SimpleGraph.mem_neighborFinset]
        exact and_iff_right_of_imp (fun hw =>
          SimpleGraph.isBipartiteWith_neighborFinset_subset h hv
            (by simpa only [SimpleGraph.mem_neighborFinset] using hw))
      rw [hnbr, H.card_neighborFinset_eq_degree]
    _ = _ := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges h

/-- Corollary 3.4: the dense bipartite minor bound with possibly unequal sides. -/
theorem unequalBipMinor (K : ℝ) (hK : 0 < K) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ n : ℕ, ∀ H : SimpleGraph (Fin n), ∀ A B : Finset (Fin n),
      H.IsBipartiteWith (A : Set (Fin n)) (B : Set (Fin n)) →
      A ∪ B = univ → A.card ≤ B.card → n₀ ≤ A.card →
      (1-gamma)*(A.card : ℝ)*(B.card : ℝ) ≤ H.edgeFinset.card →
      K*(A.card : ℝ)/sqrt (log (A.card : ℝ)) ≤ (hadwigerNumber H : ℝ) := by
  obtain ⟨gamma,hg,N,hN,hminor⟩ := bipMinor K hK
  refine ⟨gamma,hg,N,hN,?_⟩
  intro n H A B hbip _hcover hAB hA hedges
  have hAp : 0 < A.card := hN.trans_le hA
  have hBp : 0 < B.card := hAp.trans_le hAB
  have hden : (0 : ℝ) < (A.card : ℝ)*(B.card : ℝ) := by positivity
  have hdensity : 1-gamma ≤ (H.edgeDensity A B : ℝ) := by
    simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul]
    apply (le_div_iff₀ hden).mpr
    rw [bipartite_interedges_card H A B hbip]
    simpa only [mul_assoc] using hedges
  have hm := Main.cross_minor_unequal H A B (disjoint_coe.mp hbip.disjoint)
    hAp hBp (by simpa only [min_eq_left hAB] using hA) hminor hdensity
  simpa only [min_eq_left hAB] using hm

end HadwigerRamsey
