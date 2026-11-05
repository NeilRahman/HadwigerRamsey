import HadwigerRamsey4Col.MergingEntropy
import HadwigerRamsey4Col.ThresholdBounds

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

lemma capacityF_nonneg {t : ℝ} (ht : 0 ≤ t) (s : ℝ) : 0 ≤ capacityF t s := by
  unfold capacityF
  have he : exp (-(t/s^2)) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg ht (sq_nonneg s)))
  exact mul_nonneg (sq_nonneg _) (by linarith)

lemma capacityF_mono {t s S : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hS : s ≤ S) :
    capacityF t s ≤ capacityF t S := by
  rcases eq_or_lt_of_le hs with he | hs
  · subst s
    simpa using capacityF_nonneg ht S
  have hS0 : 0 < S := hs.trans_le hS
  have hs2 : s^2 ≤ S^2 := (sq_le_sq₀ hs.le hS0.le).mpr hS
  let u : ℝ := s^2/S^2
  have hu0 : 0 ≤ u := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hu1 : u ≤ 1 := (div_le_one (sq_pos_of_pos hS0)).mpr hs2
  have hh := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-(t/s^2)))
    (sub_nonneg.mpr hu1) hu0 (show 1-u+u=1 by ring)
  have hx : (1-u)*0+u*(-(t/s^2))=-(t/S^2) := by
    dsimp [u]
    field_simp <;> ring
  simp only [smul_eq_mul, exp_zero, mul_one] at hh
  rw [hx] at hh
  have h := mul_le_mul_of_nonneg_left hh (sq_nonneg S)
  have hf : S^2*(1-u+u*exp (-(t/s^2))) = S^2-s^2+s^2*exp (-(t/s^2)) := by
    dsimp [u]
    field_simp
  rw [hf] at h
  dsimp [capacityF]
  nlinarith

namespace FiniteProgram
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma region_capacity (P : FiniteProgram α β) (c : Fin 4) (A : Finset α) {t : ℝ}
    (hE : regionCost P.mass (P.density c) A A ≤ t) :
    regionDensity P.mass (P.density c) A A ≤ capacityF t (regionMass P.mass A) := by
  by_cases hA : A.Nonempty
  · have hs : 0 < regionMass P.mass A := sum_pos (fun i _ => P.mass_pos i) hA
    let q := blockAverage P.mass (P.density c) A A
    have hq := blockAverage_bounds P.mass (P.density c) A A P.mass_pos hA hA
      (P.density_nonneg c) (P.density_lt_one c)
    have hJ := blockAverage_cost P.mass (P.density c) A A P.mass_pos hA hA (P.density_lt_one c)
    have hcost : cost q ≤ t/(regionMass P.mass A)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
      nlinarith
    have hh := exp_le_exp.mpr (neg_le_neg hcost)
    simp only [cost, neg_neg] at hh
    rw [exp_log (sub_pos.mpr hq.2)] at hh
    have hd : (regionMass P.mass A)^2*q = regionDensity P.mass (P.density c) A A := by
      dsimp [q, blockAverage]
      field_simp
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (regionMass P.mass A))
    dsimp [capacityF]
    nlinarith
  · have he : A=∅ := not_nonempty_iff_eq_empty.mp hA
    simp [he,regionMass,regionDensity]

lemma part_capacity (P : FiniteProgram α β) {t : ℝ} (ht : P.bound ≤ t) (c : Fin 4) (b : β) :
    P.partDensity c b ≤ capacityF t (P.partMass c b) :=
  P.region_capacity c (P.part c b) ((P.entropy_le c b).trans ht)

lemma partMass_nonneg (P : FiniteProgram α β) (c : Fin 4) (b : β) : 0 ≤ P.partMass c b :=
  P.regionMass_nonneg _

lemma partMass_le_one (P : FiniteProgram α β) (c : Fin 4) (b : β) : P.partMass c b ≤ 1 := by
  have h := single_le_sum (fun b _ => P.partMass_nonneg c b) (mem_univ b)
  rwa [P.partMass_sum] at h

lemma part_linear_capacity (P : FiniteProgram α β) (ht : P.bound ≤ threshold) (c : Fin 4) (b : β) :
    P.partDensity c b ≤ (16/25 : ℝ)*sqrt threshold*P.partMass c b :=
  (P.part_capacity ht c b).trans (capacityF_bound (by norm_num) (P.partMass_nonneg c b))

end FiniteProgram
end HadwigerRamsey4Col
