import HadwigerRamsey.BipMinor.Asymptotic

open scoped Classical
open Finset Real
open HadwigerRamsey.ThomasonUpper
namespace HadwigerRamsey

/-- Lemma 3.3 (`bipMinor`): sufficiently dense balanced bipartite graphs
have arbitrarily large fixed coefficients in the Hadwiger lower bound. -/
theorem bipMinor (K : ℝ) (hK : 0 < K) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ n : ℕ, ∀ H : SimpleGraph (Fin n), ∀ A B : Finset (Fin n),
      H.IsBipartiteWith (A : Set (Fin n)) (B : Set (Fin n)) →
      A ∪ B = univ → A.card = B.card → n₀ < A.card →
      (1-gamma)*(A.card : ℝ)^2 ≤ H.edgeFinset.card →
      K*(A.card : ℝ)/sqrt (log (A.card : ℝ)) ≤ (hadwigerNumber H : ℝ) := by
  obtain ⟨gamma,hg,N,hN,hminor⟩ := BipMinor.balanced_dense_minor K hK
  refine ⟨gamma,hg,N,hN,?_⟩
  intro n H A B hbip hcover hAB hA hedges
  have hd : Disjoint A B := disjoint_coe.mp hbip.disjoint
  have hB : ∀ v, v ∈ B ↔ v ∉ A := by
    intro v
    constructor
    · intro hvB hvA; exact disjoint_left.mp hd hvA hvB
    · intro hvA
      have hv : v ∈ A ∪ B := by rw [hcover]; exact mem_univ _
      exact (mem_union.mp hv).resolve_left hvA
  let c : Fin n → Fin 2 := fun v => if v ∈ A then 0 else 1
  have hc0 : classVertices c 0 = A := by ext v; simp [classVertices,c]
  have hc1 : classVertices c 1 = B := by ext v; simp [classVertices,c,hB]
  have hp : ∀ u v, H.Adj u v → c u ≠ c v := by
    intro u v huv
    rcases hbip.mem_of_adj huv with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · change u ∈ A at hu
      change v ∈ B at hv
      have hv' := (hB v).mp hv
      simp only [c,if_pos hu,if_neg hv']
      decide
    · change u ∈ B at hu
      change v ∈ A at hv
      have hu' := (hB u).mp hu
      simp only [c,if_neg hu',if_pos hv]
      decide
  apply hminor n A.card hA H c hp ?_ hedges
  intro i
  fin_cases i
  · change (classVertices c 0).card = A.card
    rw [hc0]
  · change (classVertices c 1).card = A.card
    rw [hc1,← hAB]
end HadwigerRamsey
