import HadwigerRamsey4Col.StabilityIdentities
import HadwigerRamsey4Col.StabilityMoments

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

lemma logarithmic_diagonal_term {u S : ℝ} (hu : 0 < u) (hS : 0 < S) :
    u*log (3/2)-u*(3*u/S-1) ≤ u*log (S/(2*u)) := by
  have ht := log_le_sub_one_of_pos (div_pos (by positivity : 0 < 3*u) hS)
  have he : log (S/(2*u)) = log (3/2)-log (3*u/S) := by
    rw [log_div (ne_of_gt hS) (by positivity : 2*u ≠ 0),
      log_div (by positivity : 3*u ≠ 0) (ne_of_gt hS),
      log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hu),
      log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt hu),
      log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left ht hu.le]

lemma diagonalDual_lower {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) (i : Fin 4) :
    rowWeight a i*log (3/2)-(3*moment a 2-4*a i^2+2*a i-1)/3 ≤ diagonalDual a i := by
  have hr := (rowWeight_bounds hs hn hu i).1
  have hr0 : 0 < rowWeight a i := by linarith
  have hh := sum_le_sum (fun j (_ : j ∈ univ.erase i) =>
    logarithmic_diagonal_term (pairWeight_pos hn i j) hr0)
  simp only [sum_sub_distrib, ← sum_mul] at hh
  change rowWeight a i*log (3/2)-
    (∑ j ∈ univ.erase i, pairWeight a i j*(3*pairWeight a i j/rowWeight a i-1)) ≤
    diagonalDual a i at hh
  rw [row_penalty_identity hs i (ne_of_gt hr0)] at hh
  have hnum : 0 ≤ 3*moment a 2-4*a i^2+2*a i-1 := by
    rw [← row_variance_identity hs i]
    exact mul_nonneg (by norm_num) (sum_nonneg (fun j _ => sq_nonneg _))
  have hdiv : (3*moment a 2-4*a i^2+2*a i-1)/(4*rowWeight a i) ≤
      (3*moment a 2-4*a i^2+2*a i-1)/3 := by
    apply div_le_div_of_nonneg_left hnum (by norm_num : (0:ℝ)<3)
    linarith
  linarith

lemma diagonal_entropy_moments {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    log (3/2)*(shiftedWeight*moment a 2+moment a 3)-
      (3*(moment a 2)^2-4*moment a 4+2*moment a 3-moment a 2)/3 ≤
      ∑ i, a i^2*diagonalDual a i := by
  rw [← diagonal_moment_identity hs]
  exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (diagonalDual_lower hn hu hs i) (sq_nonneg _))

lemma offdiag_entropy_moments {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    entropy weight*(1-moment a 2)+
      entropySlope weight*((5/4 : ℝ)*moment a 2-moment a 3-1/4)-
      (2*moment a 3+(moment a 2)^2-2*moment a 4-(9/8 : ℝ)*moment a 2+1/8) ≤
    ∑ i, ∑ j ∈ univ.erase i, a i*a j*entropy (pairWeight a i j) := by
  rw [← offdiag_moment_identity hs]
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hn i) (hn j))
  exact entropy_quadratic_lower weight_bounds.1.le
    (pairWeight_shift_bound hs hu i j (ne_of_mem_erase hj).symm)

/-- The quantitative stability assertion of Proposition/Lemma 5. -/
theorem four_atom_stability {a : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ a i)
    (hu : ∀ i, a i ≤ (2/5 : ℝ)) (hs : ∑ i, a i = 1) :
    (1+6*weight)*tStar parameter+(3/100 : ℝ)*centeredMoment a 2 ≤ dualValue a := by
  have hd := diagonal_entropy_moments hn hu hs
  have ho := offdiag_entropy_moments hn hu hs
  have he := baseline_moment_identity (moment a 2) (moment a 3)
  have hp := stability_polynomial hn hu hs
  obtain ⟨hq,hr⟩ := moment_lower_bounds hn hs
  have ha := mul_le_mul_of_nonneg_right alpha_coefficient_bound.le (sub_nonneg.mpr hq)
  have hg := mul_le_mul_of_nonneg_right gamma_coefficient_bound.le (sub_nonneg.mpr hr)
  rw [← uniformValue_eq]
  dsimp [dualValue]
  nlinarith

end HadwigerRamsey4Col
