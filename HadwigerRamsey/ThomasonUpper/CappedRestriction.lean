import HadwigerRamsey.ThomasonUpper.Restriction
import HadwigerRamsey.ThomasonUpper.Capping

open scoped BigOperators Classical
open Finset Real

namespace HadwigerRamsey.ThomasonUpper

theorem restrictedLambda {n k : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (Z : Finset (Fin n)) :
    blockLambda (restrictedClasses classes Z)
      (blockDensity (restrictedGraph G Z) (restrictedClasses classes Z)) = deletedLambda G classes Z := by
  simp only [blockLambda,deletedLambda,restrictedClassMass,restrictedBlockDensity]

/-- Cap the original graph and then delete a small set of vertices.
The remaining graph has uniformly positive class masses and complement
block densities, and its entropy approximates the exact target entropy. -/
theorem exists_capped_restriction {n k : ℕ} (G : SimpleGraph (Fin n))
    (classes : Fin n → Fin k) (Z : Finset (Fin n)) {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 ≤ delta) (hdsmall : delta < epsilon/2)
    (hdq : 8*delta/epsilon ≤ epsilon/2) (hn : 4 ≤ epsilon*n)
    (hZ : (Z.card : ℝ) ≤ delta*n)
    (hmass : ∀ i, epsilon ≤ classMass classes i) :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧ Z.card < n ∧
      (∀ i, epsilon/2 ≤ classMass (restrictedClasses classes Z) i) ∧
      (∀ i j, epsilon/2 ≤ 1-blockDensity (restrictedGraph H Z) (restrictedClasses classes Z) i j) ∧
      |blockLambda (restrictedClasses classes Z)
          (blockDensity (restrictedGraph H Z) (restrictedClasses classes Z)) - cappedLambda G classes epsilon| ≤
        4/(epsilon^3*(n : ℝ)^2) + (16/epsilon^2+4*log (2/epsilon)/epsilon)*delta := by
  have hnR : (0 : ℝ) < n := by nlinarith only [hn,hepsilon,(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsize : ∀ i, epsilon*n ≤ (classVertices classes i).card := by
    intro i
    exact (le_div_iff₀ hnR).mp (hmass i)
  obtain ⟨H,hHG,hH,herr⟩ := exists_capped_subgraph_entropy G classes hepsilon hepsilon hepsilon1
    (by linarith) hsize
  have hb := vertex_deletion_bounds H classes Z hepsilon hepsilon1 hdelta hdsmall hn hZ hsize
  have hLambda := vertex_deletion_lambda_bound H classes Z hepsilon hepsilon1 hdelta hdsmall hn hZ hsize
    (fun i j => (hH i j).2) hdq
  refine ⟨H,hHG,hb.1,?_,?_,?_⟩
  · intro i
    rw [restrictedClassMass]
    unfold deletedClassMass
    have hNp : (0 : ℝ) < ((n-Z.card : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hb.1
    apply (le_div_iff₀ hNp).mpr
    have hNn : (((n-Z.card : ℕ) : ℝ)) ≤ n := by exact_mod_cast Nat.sub_le n Z.card
    have hh := mul_le_mul_of_nonneg_left hNn (show 0 ≤ epsilon/2 by positivity)
    nlinarith only [hh,hb.2.1 i]
  · intro i j
    rw [restrictedBlockDensity]
    exact hLambda.1 i j
  · rw [restrictedLambda]
    have htri := (abs_sub_le (deletedLambda H classes Z)
      (blockLambda classes (blockDensity H classes)) (cappedLambda G classes epsilon)).trans
      (add_le_add hLambda.2 herr)
    calc
      _ ≤ (16/epsilon^2+4*log (2/epsilon)/epsilon)*delta + 4/(epsilon*epsilon^2*(n : ℝ)^2) := htri
      _ = _ := by ring

end HadwigerRamsey.ThomasonUpper
