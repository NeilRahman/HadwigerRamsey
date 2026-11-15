import HadwigerRamsey.Asymptotic

open scoped Topology
open Filter Real

namespace HadwigerRamsey.ThomasonUpper

/-- Exponential concentration still beats every union bound needed in Lemma A.4
when the exponent is n divided by a fixed power of log log n. -/
theorem eventually_exp_loglog_power_le {c : ℝ} (hc : 0 < c) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      exp (-c*n*(1/log (log (n : ℝ)))^K) ≤ 1/(n : ℝ)^4 := by
  have hg := eventually_log_power_le ((K+1 : ℕ) : ℝ) 1 (c/4) (by norm_num) (by positivity)
  have hl := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (exp 2)
  filter_upwards [hg, hl, eventually_ge_atTop 3] with n hgrowth hlog hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < log (n : ℝ) := (exp_pos 2).trans_le hlog
  have hll : 2 ≤ log (log (n : ℝ)) := by
    have hh := log_le_log (exp_pos 2) hlog
    simpa only [log_exp, Function.comp_def] using hh
  have hlpos : 0 < log (log (n : ℝ)) := by linarith
  have hlL : log (log (n : ℝ)) ≤ log (n : ℝ) := by
    have hh := log_le_sub_one_of_pos hL
    linarith
  have hpow := pow_le_pow_left₀ hlpos.le hlL K
  have hgrowth' : (log (n : ℝ))^(K+1) ≤ c/4*n := by
    simpa only [rpow_natCast, rpow_one] using hgrowth
  have hmul : 4*log (n : ℝ)*(log (log (n : ℝ)))^K ≤ c*n := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4*log (n : ℝ))
    rw [pow_succ] at hgrowth'
    nlinarith
  have hexponent : 4*log (n : ℝ) ≤ c*n*(1/log (log (n : ℝ)))^K := by
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos hlpos K)).mpr hmul
  have hneg : -c*n*(1/log (log (n : ℝ)))^K ≤ -(4*log (n : ℝ)) := by linarith
  apply (exp_le_exp.mpr hneg).trans_eq
  rw [show -(4*log (n : ℝ)) = -log ((n : ℝ)^4) by rw [log_pow]; ring,
    exp_neg, exp_log (pow_pos hnR 4), one_div]

/-- The three Hoeffding failure bounds in the reservoir construction have
sum below one for all sufficiently large n, uniformly over the graph. -/
theorem reservoir_failure_eventually_lt_one {c : ℝ} (hc : 0 < c) (H : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := 1/log (log (n : ℝ))
      0 ≤ r ∧ r ≤ 1/2 ∧
      2*exp (-2*r^2*n) + n*exp (-c*r^2*n/2) +
        (n : ℝ)^2*exp (-c*n*(r^H)^2/4) < 1 := by
  have h1 := eventually_exp_loglog_power_le (by norm_num : (0:ℝ) < 2) 2
  have h2 := eventually_exp_loglog_power_le (show 0 < c/2 by positivity) 2
  have h3 := eventually_exp_loglog_power_le (show 0 < c/4 by positivity) (H*2)
  have hl := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (exp 2)
  filter_upwards [h1, h2, h3, hl, eventually_ge_atTop 3] with n hh1 hh2 hh3 hlog hn
  let r := 1/log (log (n : ℝ))
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlpos : 0 < log (n : ℝ) := (exp_pos 2).trans_le hlog
  have hll : 2 ≤ log (log (n : ℝ)) := by
    simpa only [log_exp, Function.comp_def] using log_le_log (exp_pos 2) hlog
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hll
  refine ⟨hr, hrhalf, ?_⟩
  have he1 : -2*r^2*(n : ℝ) = -(2:ℝ)*n*r^2 := by ring
  have he2 : -c*r^2*(n : ℝ)/2 = -(c/2)*n*r^2 := by ring
  have he3 : -c*(n : ℝ)*(r^H)^2/4 = -(c/4)*n*r^(H*2) := by rw [pow_mul]; ring
  rw [he1, he2, he3]
  change exp (-(2:ℝ)*n*r^2) ≤ _ at hh1
  change exp (-(c/2)*n*r^2) ≤ _ at hh2
  change exp (-(c/4)*n*r^(H*2)) ≤ _ at hh3
  have hb : 2*exp (-(2:ℝ)*n*r^2) + n*exp (-(c/2)*n*r^2) +
      (n : ℝ)^2*exp (-(c/4)*n*r^(H*2)) ≤
      (2+(n : ℝ)+(n : ℝ)^2)/(n : ℝ)^4 := by
    have ha := mul_le_mul_of_nonneg_left hh1 (by norm_num : (0:ℝ) ≤ 2)
    have hb := mul_le_mul_of_nonneg_left hh2 hnpos.le
    have hc := mul_le_mul_of_nonneg_left hh3 (sq_nonneg (n : ℝ))
    calc
      _ ≤ 2*(1/(n : ℝ)^4) + n*(1/(n : ℝ)^4) + (n : ℝ)^2*(1/(n : ℝ)^4) :=
        add_le_add (add_le_add ha hb) hc
      _ = _ := by ring
  apply hb.trans_lt
  apply (div_lt_one (pow_pos hnpos 4)).mpr
  have hsq : (3:ℝ)*(n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hfour : (3:ℝ)*(n : ℝ)^2 ≤ (n : ℝ)^3 := by nlinarith
  have hfour' : (3:ℝ)*(n : ℝ)^3 ≤ (n : ℝ)^4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n-3) (pow_nonneg hnpos.le 3)]
  nlinarith

end HadwigerRamsey.ThomasonUpper
