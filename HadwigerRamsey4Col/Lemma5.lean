import HadwigerRamsey4Col.PairingDual

open Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

/-- Relate the ordered off-diagonal convention to the manuscript's `i < j` sum. -/
theorem dualValue_eq_unordered (a : Fin 4 → ℝ) :
    dualValue a = (∑ i, a i^2*diagonalDual a i)+
      2*∑ i, ∑ j with i < j, a i*a j*entropy (pairWeight a i j) := by
  let f : Fin 4 → Fin 4 → ℝ := fun i j => a i*a j*entropy (pairWeight a i j)
  have hsym : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f]
    rw [pairWeight_symm a i j]
    ring
  have h10 := hsym 1 0
  have h20 := hsym 2 0
  have h21 := hsym 2 1
  have h30 := hsym 3 0
  have h31 := hsym 3 1
  have h32 := hsym 3 2
  change (∑ i, a i^2*diagonalDual a i)+(∑ i, ∑ j ∈ univ.erase i, f i j) =
    (∑ i, a i^2*diagonalDual a i)+2*(∑ i, ∑ j with i < j, f i j)
  simp [sum_erase_eq_sub, sum_filter, Fin.sum_univ_succ, h10,h20,h21,h30,h31,h32]
  ring

/-- Proposition 5 (the next numbered result after Lemma 4) of the analytic
manuscript: the exact quantitative four-atom stability inequality. -/
theorem lemma5 (a : Fin 4 → ℝ) (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    (1+6*weight)*tStar parameter+(3/100 : ℝ)*∑ i, (a i-1/4)^2 ≤ dualValue a :=
  four_atom_stability hn hu hs

/-- The concluding assertion of Proposition 5, for every feasible pairing
pattern, without an atom-size assumption. -/
theorem lemma5_pairing_lower_bound (I : PairingData) (t : ℝ)
    (hspan : I.spanEnergy ≤ t) (hpairs : ∀ i j, i ≠ j → I.pairEnergy i j ≤ t) :
    tStar parameter ≤ t :=
  I.optimum_lower_bound t hspan hpairs

end HadwigerRamsey4Col
