import HadwigerRamsey.Ramsey.Definition
import HadwigerRamsey.Ramsey.Scaling

open Filter Real
open scoped Topology Classical

namespace HadwigerRamsey.Ramsey

/-- Theorem 1.2 gives the lower Ramsey bound at a rounded order below
the inverse leading coefficient. -/
theorem eventually_floor_lt_ramsey {c : ℝ} (hc : 0 < c) (hcb : c < beta⁻¹) :
    ∀ᶠ k : ℕ in atTop, floorOrder c k < hadwigerRamsey k := by
  have hbc : 0 < beta*c := mul_pos beta_pos hc
  have hbc1 : beta*c < 1 := by
    have hh := (lt_div_iff₀ beta_pos).mp (show c < 1/beta by simpa using hcb)
    nlinarith only [hh]
  let ε := (1-beta*c)/(2*(beta*c))
  have hε : 0 < ε := div_pos (sub_pos.mpr hbc1) (by positivity)
  have hεeq : ε*(2*(beta*c)) = 1-beta*c := div_mul_cancel₀ _ (by positivity)
  have hcoef : (1+ε)*beta*c < 1 := by nlinarith only [hεeq,hbc1]
  obtain ⟨N, hN⟩ := existencethm ε hε
  have ht := (floorOrder_inverse_limit hc).const_mul ((1+ε)*beta)
  have hv := (tendsto_order.mp ht).2 1 hcoef
  filter_upwards [(floorOrder_atTop hc).eventually_ge_atTop N, hv,
    (eventually_ge_atTop 1 : ∀ᶠ k : ℕ in atTop, 1 ≤ k)] with k hn hk hkpos
  obtain ⟨G,hG,hGi⟩ := hN (floorOrder c k) hn
  apply lt_hadwigerRamsey G hG
  intro i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hh : (1+ε)*beta*(floorOrder c k : ℝ)/sqrt (log (floorOrder c k : ℝ)) < k := by
    have hh : ((1+ε)*beta*(floorOrder c k : ℝ)/sqrt (log (floorOrder c k : ℝ))) /
        (k : ℝ) < 1 := by simpa only [mul_div_assoc] using hk
    simpa only [one_mul] using (div_lt_iff₀ hkR).mp hh
  exact_mod_cast (hGi i).trans_lt hh

/-- Theorem 1.3 gives the upper Ramsey bound at a rounded order above
the inverse leading coefficient. -/
theorem eventually_ramsey_le_ceil {c : ℝ} (hcb : beta⁻¹ < c) :
    ∀ᶠ k : ℕ in atTop, hadwigerRamsey k ≤ ceilOrder c k := by
  have hc : 0 < c := (inv_pos.mpr beta_pos).trans hcb
  have hbc : 0 < beta*c := mul_pos beta_pos hc
  have hbc1 : 1 < beta*c := by
    have hh := (div_lt_iff₀ beta_pos).mp (show 1/beta < c by simpa using hcb)
    nlinarith only [hh]
  let ε := (beta*c-1)/(2*(beta*c))
  have hε : 0 < ε := div_pos (sub_pos.mpr hbc1) (by positivity)
  have hεeq : ε*(2*(beta*c)) = beta*c-1 := div_mul_cancel₀ _ (by positivity)
  have hcoef : 1 < (1-ε)*beta*c := by nlinarith only [hεeq,hbc1]
  obtain ⟨N, hN⟩ := mainthm ε hε
  have ht := (ceilOrder_inverse_limit hc).const_mul ((1-ε)*beta)
  have hv := (tendsto_order.mp ht).1 1 hcoef
  filter_upwards [(ceilOrder_atTop hc).eventually_ge_atTop N, hv,
    (eventually_ge_atTop 1 : ∀ᶠ k : ℕ in atTop, 1 ≤ k)] with k hn hk hkpos
  apply hadwigerRamsey_le
  intro G hG
  obtain ⟨i,hi⟩ := hN (ceilOrder c k) hn G hG
  refine ⟨i,(hasCliqueMinor_iff_le_hadwigerNumber (G i)).mpr ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hh : (k : ℝ) < (1-ε)*beta*(ceilOrder c k : ℝ)/sqrt (log (ceilOrder c k : ℝ)) := by
    have hh : 1 < ((1-ε)*beta*(ceilOrder c k : ℝ)/sqrt (log (ceilOrder c k : ℝ))) /
        (k : ℝ) := by simpa only [mul_div_assoc] using hk
    simpa only [one_mul] using (lt_div_iff₀ hkR).mp hh
  exact_mod_cast (hh.trans_le hi).le

end HadwigerRamsey.Ramsey
