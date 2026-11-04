import HadwigerRamsey.OptApprox
import HadwigerRamsey.FOpt.Constants

open scoped BigOperators
open Finset Real
namespace HadwigerRamsey.Main

theorem beta_bounds : (63/100 : ℝ) < beta ∧ beta < 1 := by
  have hb := beta_pos
  have hs : beta^2 = FOpt.c := FOpt.beta_sq
  have hc := FOpt.c_mem
  norm_num [FOpt.cI, LeanCert.Core.IntervalRat.mem_def] at hc
  constructor <;> nlinarith only [hb,hs,hc.1,hc.2]

/-- The logarithmic cost lies below its chord on the capped interval. -/
theorem logCost_chord {ζ p : ℝ} (hz : 0 < ζ) (hz1 : ζ < 1)
    (hp : 0 ≤ p) (hpcap : p ≤ 1-ζ) :
    -log (1-p) ≤ (-log ζ)/(1-ζ)*p := by
  let t := p/(1-ζ)
  have ht : 0 ≤ t := div_nonneg hp (by linarith)
  have ht1 : t ≤ 1 := (div_le_one (by linarith : 0 < 1-ζ)).mpr hpcap
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show ζ ∈ Set.Ioi 0 from hz) (by linarith : 0 ≤ 1-t) ht (by ring : 1-t+t=1)
  have he : (1-t)*1+t*ζ = 1-p := by dsimp [t]; field_simp [(sub_pos.mpr hz1).ne'] <;> ring
  simp only [smul_eq_mul, log_one, mul_zero, zero_add,he] at hh
  dsimp [t] at hh
  calc
    -log (1-p) ≤ -(p/(1-ζ)*log ζ) := neg_le_neg hh
    _ = _ := by ring

theorem capped_log_factor {ζ : ℝ} (hz : 0 < ζ) (hz1 : ζ < 1) :
    0 ≤ (-log ζ)/(1-ζ) ∧ ζ*((-log ζ)/(1-ζ)) ≤ 1 := by
  have hl := log_nonpos hz.le hz1.le
  have hh := log_le_sub_one_of_pos (inv_pos.mpr hz)
  rw [log_inv] at hh
  have hb : ζ*(-log ζ) ≤ 1-ζ := by
    have h := mul_le_mul_of_nonneg_left hh hz.le
    rw [mul_sub, mul_inv_cancel₀ hz.ne',mul_one] at h
    exact h
  refine ⟨div_nonneg (by linarith) (by linarith),?_⟩
  rw [← mul_div_assoc]
  exact (div_le_one (by linarith : 0 < 1-ζ)).mpr hb

end HadwigerRamsey.Main
