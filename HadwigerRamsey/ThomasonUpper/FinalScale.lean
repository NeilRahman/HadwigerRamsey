import HadwigerRamsey.ThomasonUpper.Density

open scoped Topology
open Real Filter

namespace HadwigerRamsey.ThomasonUpper

/-- Uniform square-root error conversion, including the loss of reservoir
vertices. The final error remains outside the square root. -/
theorem final_entropy_accuracy {Gamma R B epsilon eta d : ℝ}
    (hGamma : 0 ≤ Gamma) (hR : 0 ≤ R) (hB : Gamma ≤ B)
    (hepsilon : 0 < epsilon) (heta : 0 ≤ eta) (heta1 : eta < 1)
    (hd : 0 ≤ d) (hdeta : d ≤ eta)
    (hcost : 4*eta*sqrt B ≤ epsilon)
    (herr : |R-Gamma| ≤ (epsilon/4)^2) :
    sqrt Gamma-epsilon ≤ (1-eta)*(1-d)*sqrt R := by
  have hsG := sqrt_nonneg Gamma
  have hsR := sqrt_nonneg R
  have hsB := sqrt_le_sqrt hB
  have hs : sqrt Gamma ≤ sqrt R+epsilon/4 := by
    have hh := (abs_le.mp herr).1
    have hGsq := sq_sqrt hGamma
    have hRsq := sq_sqrt hR
    nlinarith only [hh,hGsq,hRsq,hsG,hsR,hepsilon,sq_nonneg (sqrt Gamma-sqrt R-epsilon/4)]
  have hcoef : 0 ≤ (1-eta)*(1-d) := mul_nonneg (by linarith) (by linarith)
  have hcoef1 : (1-eta)*(1-d) ≤ 1 := by nlinarith
  have hcoeflow : 1-2*eta ≤ (1-eta)*(1-d) := by nlinarith
  have hlose : 2*eta*sqrt Gamma ≤ epsilon/2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left (show sqrt Gamma-epsilon/4 ≤ sqrt R by linarith) hcoef
  have hh' := mul_le_mul_of_nonneg_right hcoeflow hsG
  have hh'' := mul_le_mul_of_nonneg_right hcoef1 (show 0 ≤ epsilon/4 by positivity)
  nlinarith only [hh,hh',hh'',hlose,hepsilon]

/-- For a retained linear fraction of the vertices, the two logarithmic
normalizations differ by at most a constant factor. -/
theorem sqrt_log_order_comparison {n N : ℕ} (hN : 2 ≤ N) (hNn : N ≤ n)
    (hnN : n ≤ 2*N) :
    0 < sqrt (log (N : ℝ)) ∧
      sqrt (log (N : ℝ)) ≤ sqrt (log (n : ℝ)) ∧
      sqrt (log (n : ℝ)) ≤ 2*sqrt (log (N : ℝ)) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hnR : (n : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hnN
  have hlogN : 0 < log (N : ℝ) := log_pos (by linarith)
  have hlogs := log_le_log hNp (show (N : ℝ) ≤ n by exact_mod_cast hNn)
  have hlogn : log (n : ℝ) ≤ 2*log (N : ℝ) := by
    have hnpos : (0 : ℝ) < n := by
      have hh : (N : ℝ) ≤ n := by exact_mod_cast hNn
      linarith only [hNp,hh]
    have hh := log_le_log hnpos hnR
    rw [log_mul (by norm_num) hNp.ne'] at hh
    have hh' := log_le_log (by norm_num : (0 : ℝ) < 2) hNR
    linarith
  refine ⟨sqrt_pos.mpr hlogN,sqrt_le_sqrt hlogs,?_⟩
  have hnnon : 0 ≤ log (n : ℝ) := hlogN.le.trans hlogs
  nlinarith only [sq_sqrt hnnon,sq_sqrt hlogN.le,sqrt_nonneg (log (n : ℝ)),
    sqrt_nonneg (log (N : ℝ)),hlogn]

end HadwigerRamsey.ThomasonUpper
