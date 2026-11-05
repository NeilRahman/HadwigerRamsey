import HadwigerRamsey4Col.StabilityEntropy
import HadwigerRamsey4Col.LargeAtom
import HadwigerRamsey4Col.WeightedCosts

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col
namespace PairingData

noncomputable def weightedEnergy (I : PairingData) : ℝ :=
  I.spanEnergy+(1/2 : ℝ)*∑ i, ∑ j ∈ univ.erase i, pairWeight I.mass i j*I.pairEnergy i j

lemma diagonal_dual_bound (I : PairingData) (hu : ∀ i, I.mass i ≤ (2/5 : ℝ)) (i : Fin 4) :
    diagonalDual I.mass i ≤ cost (I.span i i)+
      ∑ j ∈ univ.erase i, pairWeight I.mass i j*cost (I.diag i j) := by
  have hS := rowWeight_bounds I.mass_sum I.mass_nonneg hu i
  have hS0 : 0 < rowWeight I.mass i := by linarith [hS.1]
  have hspan := cost_ge_self (I.span_lt_one i i)
  have hterms := sum_le_sum (fun j (hj : j ∈ univ.erase i) =>
    weighted_diagonal_cost (pairWeight_pos I.mass_nonneg i j) hS0
      (I.diag_lt_one i j (ne_of_mem_erase hj).symm))
  have hc : (univ.erase i).card = 3 := by simp
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
    ← mul_sum, hc, Nat.cast_ofNat] at hterms
  change diagonalDual I.mass i+(rowWeight I.mass i/2)*
      (∑ j ∈ univ.erase i, I.diag i j)-3*(rowWeight I.mass i/2)+rowWeight I.mass i ≤
      ∑ j ∈ univ.erase i, pairWeight I.mass i j*cost (I.diag i j) at hterms
  have hs := I.diag_sum i
  have hn := I.span_nonneg i i
  have hm : 0 ≤ (1-rowWeight I.mass i/2)*I.span i i := by
    exact mul_nonneg (by linarith [hS.2]) hn
  nlinarith

lemma weightedEnergy_identity (I : PairingData) :
    I.weightedEnergy =
    (∑ i, I.mass i^2*(cost (I.span i i)+
      ∑ j ∈ univ.erase i, pairWeight I.mass i j*cost (I.diag i j)))+
    ∑ i, ∑ j ∈ univ.erase i, I.mass i*I.mass j*
      (cost (I.span i j)+pairWeight I.mass i j*cost (I.pair i j)) := by
  simp [weightedEnergy, spanEnergy, pairEnergy, pairWeight,
    sum_erase_eq_sub, Fin.sum_univ_succ]
  ring

/-- The weighted dual inequality preceding Proposition 5. -/
theorem dual_bound (I : PairingData) (hu : ∀ i, I.mass i ≤ (2/5 : ℝ)) :
    dualValue I.mass ≤ I.weightedEnergy := by
  rw [weightedEnergy_identity]
  apply add_le_add
  · exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (I.diagonal_dual_bound hu i) (sq_nonneg _))
  · apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (I.mass_nonneg i) (I.mass_nonneg j))
    exact weighted_two_colour_cost (pairWeight_pos I.mass_nonneg i j)
      (I.span_lt_one i j) (I.pair_lt_one i j (ne_of_mem_erase hj).symm)
      (I.offdiag_sum i j (ne_of_mem_erase hj).symm)

lemma weightedEnergy_upper (I : PairingData) (t : ℝ) (hspan : I.spanEnergy ≤ t)
    (hpairs : ∀ i j, i ≠ j → I.pairEnergy i j ≤ t) :
    I.weightedEnergy ≤ (1+6*weight)*t := by
  have hh : (∑ i, ∑ j ∈ univ.erase i, pairWeight I.mass i j*I.pairEnergy i j) ≤
      ∑ i, ∑ j ∈ univ.erase i, pairWeight I.mass i j*t := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hpairs i j (ne_of_mem_erase hj).symm)
      (pairWeight_pos I.mass_nonneg i j).le
  have hw : (∑ i, ∑ j ∈ univ.erase i, pairWeight I.mass i j) = 12*weight := by
    change (∑ i, rowWeight I.mass i) = _
    simp_rw [rowWeight_eq I.mass_sum]
    simp [sum_add_distrib, I.mass_sum, shiftedWeight]
    ring
  simp only [← sum_mul] at hh
  rw [hw] at hh
  dsimp [weightedEnergy]
  nlinarith

/-- The final conclusion of Proposition 5: a common upper bound on all
seven feasible component entropies cannot be smaller than `tStar parameter`. -/
theorem optimum_lower_bound (I : PairingData) (t : ℝ) (hspan : I.spanEnergy ≤ t)
    (hpairs : ∀ i j, i ≠ j → I.pairEnergy i j ≤ t) : tStar parameter ≤ t := by
  by_contra ht
  have ht' : t < tStar parameter := lt_of_not_ge ht
  have hu' := lemma3_at_optimum I (hspan.trans ht'.le)
    (fun i j hij => (hpairs i j hij).trans ht'.le)
  have hu := fun i => (hu' i).le
  have hN := four_atom_stability I.mass_nonneg hu I.mass_sum
  have hD := I.dual_bound hu
  have hU := I.weightedEnergy_upper t hspan hpairs
  have hQ : 0 ≤ centeredMoment I.mass 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have hw := weight_equation.1
  have hpos : 0 < (1+6*weight)*(tStar parameter-t) := by
    exact mul_pos (by linarith) (sub_pos.mpr ht')
  nlinarith

end PairingData
end HadwigerRamsey4Col
