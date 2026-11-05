import HadwigerRamsey4Col.StabilityData

open Real Finset
open scoped BigOperators
namespace HadwigerRamsey4Col

lemma uniformValue_eq : uniformValue = (1+6*weight)*tStar parameter := by
  have hw := weight_equation.1
  have hp := parameter_spec.1
  have hw1 : 0 < 1+weight := by linarith
  have he : 1+weight = parameter⁻¹ := by
    dsimp [weight]
    field_simp [ne_of_gt hp]
    ring
  have hlog := congrArg log weight_equation.2
  rw [log_mul (ne_of_gt hw) (pow_ne_zero 5 (ne_of_gt hw1)), log_pow] at hlog
  have hl : log (1+weight) = -log parameter := by rw [he, log_inv]
  dsimp [uniformValue, entropy, tStar]
  nlinarith [hlog, hl]

lemma diagonal_moment_identity {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1) :
    (∑ i, a i^2*(rowWeight a i*log (3/2)-
      (3*moment a 2-4*a i^2+2*a i-1)/3)) =
    log (3/2)*(shiftedWeight*moment a 2+moment a 3)-
      (3*(moment a 2)^2-4*moment a 4+2*moment a 3-moment a 2)/3 := by
  simp_rw [rowWeight_eq hs]
  simp [moment, Fin.sum_univ_succ]
  ring

lemma offdiag_moment_identity {a : Fin 4 → ℝ} (hs : ∑ i, a i = 1) :
    (∑ i, ∑ j ∈ univ.erase i, a i*a j*
      (entropy weight+entropySlope weight*((a i+a j-1/2)/2)-2*((a i+a j-1/2)/2)^2)) =
    entropy weight*(1-moment a 2)+
      entropySlope weight*((5/4 : ℝ)*moment a 2-moment a 3-1/4)-
      (2*moment a 3+(moment a 2)^2-2*moment a 4-(9/8 : ℝ)*moment a 2+1/8) := by
  have hs' : a 3 = 1-a 0-a 1-a 2 := by
    simp [Fin.sum_univ_succ] at hs
    linarith
  simp [moment, sum_erase_eq_sub, Fin.sum_univ_succ, hs']
  ring

lemma baseline_moment_identity (q r : ℝ) :
    log (3/2)*(shiftedWeight*q+r)+entropy weight*(1-q)+
      entropySlope weight*((5/4 : ℝ)*q-r-1/4)-uniformValue =
    alphaCoefficient*(q-1/4)+gammaCoefficient*(r-1/16) := by
  dsimp [alphaCoefficient, gammaCoefficient, shiftedWeight, uniformValue]
  ring

end HadwigerRamsey4Col
