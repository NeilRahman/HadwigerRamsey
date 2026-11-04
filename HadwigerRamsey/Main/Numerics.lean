import HadwigerRamsey.Main.Analytic

open Real
namespace HadwigerRamsey.Main
set_option maxHeartbeats 2000000

theorem degenerate_log_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 31/100) :
    -log (1-p) ≤ (38/100 : ℝ) := by
  have hlog : -(38/100 : ℝ) ≤ log (69/100 : ℝ) := by
    let J : LeanCert.Core.IntervalRat := ⟨-38/100,-37/100,by norm_num⟩
    have hh := LeanCert.Core.IntervalRat.mem_logPointComputable
      (q := 69/100) (by norm_num) 20
    have he := FOpt.enlarge (J := J) hh (by decide +kernel)
    norm_num [J,LeanCert.Core.IntervalRat.mem_def] at he
    norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] at he
    convert he.1 using 1 <;> norm_num
  have hh := log_le_log (by norm_num : (0:ℝ)<69/100)
    (show (69/100:ℝ) ≤ 1-p by linarith)
  linarith only [hh,hlog]

theorem degenerate_cost_bound {p α ζ : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 31/100)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hz : ζ ≤ beta/100) :
    α*sqrt (-log (1-p)) ≤ beta-ζ := by
  have hb := beta_pos
  have hs : beta^2 = FOpt.c := FOpt.beta_sq
  have hc := FOpt.c_mem
  norm_num [FOpt.cI,LeanCert.Core.IntervalRat.mem_def] at hc
  have hcost := degenerate_log_bound hp hp1
  have hsqrt : sqrt (-log (1-p)) ≤ 99*beta/100 := by
    apply (sqrt_le_left (by positivity)).mpr
    nlinarith only [hs,hc.1,hcost]
  have hh := mul_le_mul_of_nonneg_right hα1 (sqrt_nonneg (-log (1-p)))
  nlinarith only [hh,hsqrt,hz]

theorem connected_cost_gap {ε θ ζ x : ℝ} (hε : 0 < ε)
    (hθζ : θ+ζ ≤ ε*beta) (hx : x ≤ (1-ε)*beta+θ) : x ≤ beta-ζ := by
  linarith

theorem connected_energy_gap {ε r θ E : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 0 ≤ r) (hrε : r ≤ ε/100) (hθ : θ ≤ ε*beta/100)
    (hE : 0 ≤ E)
    (hbound : (1-r)*sqrt E ≤ (1-ε)*beta+θ) : E ≤ (1-ε/2)*beta^2 := by
  have hb := beta_pos
  have hr1 : r < 1 := by linarith
  have hm : r*beta ≤ ε*beta/100 := by nlinarith only [mul_le_mul_of_nonneg_right hrε hb.le]
  have hpos : 0 ≤ ε*r*beta := by positivity
  have hcmp : (1-ε)*beta+θ ≤ (1-r)*((1-ε/2)*beta) := by
    have hp : 0 ≤ ε*beta := by positivity
    nlinarith only [hm,hθ,hpos,hp]
  have hs : sqrt E ≤ (1-ε/2)*beta :=
    (mul_le_mul_iff_right₀ (by linarith : 0 < 1-r)).mp (by nlinarith only [hbound,hcmp])
  have hsq := sq_le_sq₀ (sqrt_nonneg E) (mul_nonneg (by linarith) hb.le : 0 ≤ (1-ε/2)*beta) |>.mpr hs
  rw [sq_sqrt hE] at hsq
  have ht : (1-ε/2)^2 ≤ 1-ε/2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right ht (sq_nonneg beta)
  nlinarith only [hsq,hh]

theorem sparse_energy_gap {ε ζ e E : ℝ} (hε1 : ε ≤ 1)
    (hz : 0 < ζ) (hz1 : ζ < 1) (he : e ≤ ζ*beta^2/100)
    (hE : E ≤ 7*e*((-log ζ)/(1-ζ))) : E ≤ (1-ε/2)*beta^2 := by
  have hfac := capped_log_factor hz hz1
  have hh := mul_le_mul_of_nonneg_right he hfac.1
  have hh' := mul_le_mul_of_nonneg_right hfac.2 (sq_nonneg beta)
  nlinarith only [hE,hh,hh',hε1,sq_nonneg beta]

theorem full_energy_gap {ε ζ E F : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hz : 0 ≤ ζ) (hzε : ζ ≤ ε*beta/100)
    (hE : E ≤ (1-ε/2)*beta^2) (hF : F ≤ E+ε*beta^2/10) :
    sqrt F ≤ beta-ζ := by
  have hb := beta_pos
  have hh := mul_le_mul_of_nonneg_right hzε hb.le
  have hβζ : 0 ≤ beta-ζ := by
    have hεβ := mul_le_mul_of_nonneg_right hε1 hb.le
    nlinarith only [hzε,hεβ,hb]
  apply (sqrt_le_left hβζ).mpr
  have hεβ : 0 ≤ ε*beta^2 := by positivity
  nlinarith only [hh,hE,hF,sq_nonneg ζ,hεβ]

end HadwigerRamsey.Main
