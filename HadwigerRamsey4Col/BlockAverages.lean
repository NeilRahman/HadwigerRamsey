import HadwigerRamsey4Col.FiniteProgram

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

lemma weighted_cost_average {ι : Type} [DecidableEq ι] (S : Finset ι)
    (w q : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ S, w i) (hq : ∀ i ∈ S, q i < 1) :
    cost ((∑ i ∈ S, w i*q i)/(∑ i ∈ S, w i)) ≤
      (∑ i ∈ S, w i*cost (q i))/(∑ i ∈ S, w i) := by
  let W := ∑ i ∈ S, w i
  have hsum : (∑ i ∈ S, w i/W) = 1 := by
    rw [← sum_div, div_self (ne_of_gt hW)]
  have hh := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun i hi => div_nonneg (hw i hi) hW.le) hsum
    (fun i hi => (show 1-q i ∈ Set.Ioi (0:ℝ) by exact sub_pos.mpr (hq i hi)))
  simp only [smul_eq_mul] at hh
  have hd : (∑ i ∈ S, w i/W*(1-q i)) = 1-(∑ i ∈ S, w i*q i)/W := by
    simp only [mul_sub, mul_one, sum_sub_distrib, div_mul_eq_mul_div, ← sum_div]
    change W/W-_ = _
    rw [div_self (ne_of_gt hW)]
  have he : (∑ i ∈ S, w i/W*log (1-q i)) = -(∑ i ∈ S, w i*cost (q i))/W := by
    simp [cost, div_mul_eq_mul_div, ← sum_div]
  rw [hd, he] at hh
  change -log (1-(∑ i ∈ S, w i*q i)/(∑ i ∈ S, w i)) ≤
    (∑ i ∈ S, w i*cost (q i))/(∑ i ∈ S, w i)
  rw [neg_div] at hh
  dsimp only [W] at hh
  linarith

noncomputable def blockAverage {α : Type} [Fintype α] (mass : α → ℝ)
    (p : α → α → ℝ) (A B : Finset α) : ℝ :=
  regionDensity mass p A B/(regionMass mass A*regionMass mass B)

lemma region_mass_product {α : Type} [Fintype α] (mass : α → ℝ) (A B : Finset α) :
    regionMass mass A*regionMass mass B = ∑ i ∈ A, ∑ j ∈ B, mass i*mass j := by
  simp [regionMass, sum_mul_sum]

lemma blockAverage_cost {α : Type} [Fintype α] [DecidableEq α]
    (mass : α → ℝ) (p : α → α → ℝ) (A B : Finset α)
    (hm : ∀ i, 0 < mass i) (hA : A.Nonempty) (hB : B.Nonempty)
    (hp : ∀ i j, p i j < 1) :
    regionMass mass A*regionMass mass B*cost (blockAverage mass p A B) ≤
      regionCost mass p A B := by
  have hW : 0 < ∑ ij ∈ A ×ˢ B, mass ij.1*mass ij.2 := by
    exact sum_pos (fun ij _ => mul_pos (hm _) (hm _)) (hA.product hB)
  have hh := weighted_cost_average (A ×ˢ B) (fun ij => mass ij.1*mass ij.2)
    (fun ij => p ij.1 ij.2) (fun ij _ => (mul_pos (hm _) (hm _)).le) hW
    (fun ij _ => hp _ _)
  simp only [sum_product] at hh hW
  rw [← region_mass_product] at hW
  simp only [← region_mass_product] at hh
  change cost (blockAverage mass p A B) ≤ regionCost mass p A B/(regionMass mass A*regionMass mass B) at hh
  simpa only [mul_comm] using (le_div_iff₀ hW).mp hh

lemma blockAverage_bounds {α : Type} [Fintype α] [DecidableEq α]
    (mass : α → ℝ) (p : α → α → ℝ) (A B : Finset α)
    (hm : ∀ i, 0 < mass i) (hA : A.Nonempty) (hB : B.Nonempty)
    (hp0 : ∀ i j, 0 ≤ p i j) (hp1 : ∀ i j, p i j < 1) :
    0 ≤ blockAverage mass p A B ∧ blockAverage mass p A B < 1 := by
  have hW : 0 < regionMass mass A*regionMass mass B := by
    exact mul_pos (sum_pos (fun i _ => hm i) hA) (sum_pos (fun i _ => hm i) hB)
  constructor
  · exact div_nonneg (sum_nonneg (fun i _ => sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hm _).le (hm _).le) (hp0 _ _)))) hW.le
  · apply (div_lt_one hW).mpr
    rw [region_mass_product]
    apply sum_lt_sum_of_nonempty hA
    intro i hi
    apply sum_lt_sum_of_nonempty hB
    intro j hj
    exact mul_lt_of_lt_one_right (mul_pos (hm i) (hm j)) (hp1 i j)

lemma blockAverage_symm {α : Type} [Fintype α] (mass : α → ℝ) (p : α → α → ℝ)
    (hs : ∀ i j, p i j = p j i) (A B : Finset α) :
    blockAverage mass p A B = blockAverage mass p B A := by
  unfold blockAverage regionDensity
  rw [sum_comm, mul_comm (regionMass mass A)]
  congr 1
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hs j i]
  ring

end HadwigerRamsey4Col
