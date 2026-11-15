import Mathlib

open Real

namespace HadwigerRamsey.ThomasonUpper

/-- Uniform auxiliary constants for the complete-family alternative to Lemma A.3.
The gain and ratio conditions implement the same entropy-margin argument. -/
theorem exists_multitype_asymptotic_parameters {a lambda eta : ℝ}
    (ha : 0 < a) (hlambda : 0 < lambda) (heta : 0 < eta) :
    ∃ gamma xi tau phi omega : ℝ,
      0 < gamma ∧ 0 < xi ∧ 3*xi ≤ 1 ∧
      0 < tau ∧ tau < 1 ∧ 0 < phi ∧ phi < 1 ∧ 1 ≤ omega ∧
      1-eta < (1-2*xi)/(1+gamma) ∧
      1+2*xi < (1+gamma)^2*(1-3*xi) ∧
      tau/a ≤ xi*lambda ∧ phi*log (1/tau) ≤ xi*lambda ∧
      4/(omega*phi) ≤ xi := by
  let gamma := min eta 1/8
  have hgamma : 0 < gamma := div_pos (lt_min heta (by norm_num)) (by norm_num)
  have hgeta : gamma ≤ eta/8 := div_le_div_of_nonneg_right (min_le_left eta 1) (by norm_num)
  have hg1 : gamma ≤ 1/8 := div_le_div_of_nonneg_right (min_le_right eta 1) (by norm_num)
  let xi := gamma/(12*(1+gamma)^2)
  have hden : 0 < 12*(1+gamma)^2 := by positivity
  have hxi : 0 < xi := div_pos hgamma hden
  have hxibound : xi ≤ gamma/12 := by
    apply div_le_div_of_nonneg_left hgamma.le (by norm_num)
    nlinarith [sq_nonneg gamma]
  have hxiid : xi*12*(1+gamma)^2 = gamma := by dsimp only [xi]; field_simp
  have hxi1 : 3*xi ≤ 1 := by linarith
  have hratio : 1-eta < (1-2*xi)/(1+gamma) := by
    apply (lt_div_iff₀ (by linarith : 0 < 1+gamma)).mpr
    nlinarith [mul_nonneg heta.le hgamma.le]
  have hgain : 1+2*xi < (1+gamma)^2*(1-3*xi) := by
    have heq : (1+gamma)^2*(1-3*xi) = (1+gamma)^2-gamma/4 := by nlinarith [hxiid]
    rw [heq]
    nlinarith [sq_nonneg gamma]
  let tau := min (1/2 : ℝ) (a*xi*lambda/2)
  have htau : 0 < tau := lt_min (by norm_num) (by positivity)
  have htau1 : tau < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htauloss : tau/a ≤ xi*lambda := by
    apply (div_le_iff₀ ha).mpr
    have hh : tau ≤ a*xi*lambda/2 := min_le_right _ _
    nlinarith [mul_pos (mul_pos ha hxi) hlambda]
  have hlog : 0 ≤ log (1/tau) := log_nonneg ((le_div_iff₀ htau).mpr (by linarith))
  let phi := min (1/2 : ℝ) (xi*lambda/(2*(log (1/tau)+1)))
  have hlogden : 0 < 2*(log (1/tau)+1) := by linarith
  have hphi : 0 < phi := lt_min (by norm_num) (div_pos (mul_pos hxi hlambda) hlogden)
  have hphi1 : phi < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hphiloss : phi*log (1/tau) ≤ xi*lambda := by
    have hh : phi ≤ xi*lambda/(2*(log (1/tau)+1)) := min_le_right _ _
    have hh' := (le_div_iff₀ hlogden).mp hh
    nlinarith [mul_nonneg hphi.le hlog]
  let omega := max 1 (4/(xi*phi))
  have homega : 1 ≤ omega := le_max_left _ _
  have homega0 : 0 < omega := by linarith
  have homegaloss : 4/(omega*phi) ≤ xi := by
    apply (div_le_iff₀ (mul_pos homega0 hphi)).mpr
    have hh : 4/(xi*phi) ≤ omega := le_max_right _ _
    have hh' := (div_le_iff₀ (mul_pos hxi hphi)).mp hh
    nlinarith
  exact ⟨gamma,xi,tau,phi,omega,hgamma,hxi,hxi1,htau,htau1,hphi,hphi1,homega,
    hratio,hgain,htauloss,hphiloss,homegaloss⟩

end HadwigerRamsey.ThomasonUpper
