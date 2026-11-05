import HadwigerRamsey4Col.Parameters
import Mathlib.Analysis.Convex.Deriv

open Real Set
namespace HadwigerRamsey4Col

noncomputable def entropy (x : ℝ) : ℝ := (1+x)*log (1+x)-x*log x
noncomputable def entropySlope (x : ℝ) : ℝ := log ((1+x)/x)
noncomputable def weight : ℝ := (1-parameter)/parameter
noncomputable def shiftedWeight : ℝ := 3*weight-1/4
noncomputable def alphaCoefficient : ℝ :=
  shiftedWeight*log (3/2)-entropy weight+(5/4 : ℝ)*entropySlope weight
noncomputable def gammaCoefficient : ℝ := log (3/2)-entropySlope weight

lemma weight_equation : 0 < weight ∧ weight*(1+weight)^5 = (3/2 : ℝ) := by
  obtain ⟨hp0,hp1,hp⟩ := parameter_spec
  constructor
  · exact div_pos (sub_pos.mpr hp1) hp0
  · dsimp [weight]
    field_simp [ne_of_gt hp0]
    nlinarith [hp]

lemma weight_bounds : (1/3 : ℝ) < weight ∧ weight < 11/32 := by
  obtain ⟨hw0,hw⟩ := weight_equation
  constructor
  · by_contra hn
    have hh : weight*(1+weight)^5 ≤ (1/3 : ℝ)*(1+1/3)^5 := by
      gcongr <;> linarith
    norm_num at hh
    linarith
  · by_contra hn
    have hh : (11/32 : ℝ)*(1+11/32)^5 ≤ weight*(1+weight)^5 := by
      gcongr <;> linarith
    norm_num at hh
    linarith

lemma entropy_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt entropy (entropySlope x) x := by
  have hx1 : (1+x) ≠ 0 := by linarith
  have h := (((hasDerivAt_const x 1).add (hasDerivAt_id x)).mul
    (((hasDerivAt_id x).const_add 1).log hx1)).sub
    ((hasDerivAt_id x).mul (hasDerivAt_log (ne_of_gt hx)))
  apply h.congr_deriv
  change (0+1)*log (1+x)+(1+x)*(1/(1+x))-(1*log x+x*x⁻¹) = entropySlope x
  dsimp [entropySlope]
  rw [log_div hx1 (ne_of_gt hx)]
  field_simp [hx1, ne_of_gt hx]
  ring

lemma entropySlope_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt entropySlope (-1/(x*(1+x))) x := by
  have hx1 : (1+x) ≠ 0 := by linarith
  have h := (((hasDerivAt_id x).const_add 1).div (hasDerivAt_id x)
    (ne_of_gt hx)).log (div_ne_zero hx1 (ne_of_gt hx))
  apply h.congr_deriv
  change (1*x-(1+x)*1)/x^2/((1+x)/x) = -1/(x*(1+x))
  field_simp [hx1, ne_of_gt hx]
  ring

end HadwigerRamsey4Col
