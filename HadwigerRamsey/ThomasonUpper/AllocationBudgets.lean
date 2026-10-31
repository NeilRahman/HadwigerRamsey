import HadwigerRamsey.ThomasonUpper.ReservoirAsymptotic

open scoped Topology
open Filter Real

namespace HadwigerRamsey.ThomasonUpper

/-- Fixed powers of log log n are negligible compared with sqrt(log n).
This is the growth estimate used for the two reservoir allocation budgets. -/
theorem eventually_loglog_pow_le_sqrt_log (K : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (log (log (n : ℝ)))^K ≤ c*sqrt (log (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (K : ℝ) (by norm_num : (0:ℝ) < 1/2)).bound hc
  have h' := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually h
  have hL := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [h',hL] with n hh hlog
  change 1 ≤ log (n : ℝ) at hlog
  change ‖(log (log (n : ℝ)))^(K : ℝ)‖ ≤ c*‖(log (n : ℝ))^(1/2 : ℝ)‖ at hh
  have hll : 0 ≤ log (log (n : ℝ)) := log_nonneg hlog
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg hll _),
    abs_of_nonneg (rpow_nonneg (by linarith : 0 ≤ log (n : ℝ)) _),rpow_natCast,
    ← sqrt_eq_rpow] at hh
  exact hh

/-- Once the number of parts is at most C n/sqrt(log n) and each
dominating set has size at most A log log n, both of the manuscript's
reservoir allocation budgets hold uniformly. -/
theorem eventually_allocation_budgets {ε C A : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hA : 0 < A) (H : ℕ) (hH : 1 ≤ H) :
    ∀ᶠ n : ℕ in atTop, ∀ m L : ℕ,
      (m : ℝ) ≤ C*n/sqrt (log (n : ℝ)) →
      (L : ℝ) ≤ A*log (log (n : ℝ)) →
      let r := 1/log (log (n : ℝ))
      (m : ℝ)*L ≤ ε*r*n/4 ∧
        (((H-1)*(m*L) : ℕ) : ℝ) < ε*n*r^(H-1)/4 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hd := eventually_loglog_pow_le_sqrt_log 2 (show 0 < ε/(4*C*A) by positivity)
  have hp := eventually_loglog_pow_le_sqrt_log H (show 0 < ε/(8*H*C*A) by positivity)
  have ht := (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  filter_upwards [hd,hp,ht,eventually_ge_atTop 1] with n hd hp ht hn
  intro m L hm hL
  let t := log (log (n : ℝ))
  let s := sqrt (log (n : ℝ))
  have ht1 : 1 ≤ t := ht
  have ht0 : 0 < t := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 < log (n : ℝ) := by
    have hh := (log_pos_iff (log_natCast_nonneg n)).mp
      (show 0 < log (log (n : ℝ)) from ht0)
    linarith
  have hs0 : 0 < s := sqrt_pos.mpr hlogpos
  have hml : (m : ℝ)*L*s ≤ C*A*n*t := by
    have hm' := (le_div_iff₀ hs0).mp hm
    have hh := mul_le_mul hm' hL (Nat.cast_nonneg L) (mul_pos hC hn0).le
    nlinarith
  have hdp : 4*C*A*t^2 ≤ ε*s := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C*A)).mp
      (by convert hd using 1 <;> dsimp [t,s] <;> ring : t^2 ≤ ε*s/(4*C*A))
    nlinarith
  have hpp : 8*(H : ℝ)*C*A*t^H ≤ ε*s := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*(H : ℝ)*C*A)).mp
      (by convert hp using 1 <;> dsimp [t,s] <;> ring : t^H ≤ ε*s/(8*H*C*A))
    nlinarith
  have hdom : 4*t*((m : ℝ)*L) ≤ ε*n := by
    apply (mul_le_mul_iff_right₀ hs0).mp
    have h1 := mul_le_mul_of_nonneg_left hml (by positivity : 0 ≤ 4*t)
    have h2 := mul_le_mul_of_nonneg_right hdp hn0.le
    nlinarith
  constructor
  · change (m : ℝ)*L ≤ ε*(1/t)*n/4
    have he : ε*(1/t)*(n : ℝ)/4 = ε*n/(4*t) := by ring
    rw [he]
    exact (le_div_iff₀ (by positivity : 0 < 4*t)).mpr (by nlinarith)
  · have htPow : 0 < t^(H-1) := pow_pos ht0 _
    have hid : t^(H-1)*t = t^H := by
      rw [← pow_succ]
      congr 1
      omega
    have hpstrict : 4*(H : ℝ)*C*A*t^H < ε*s := by nlinarith [mul_pos hε hs0]
    have hpath : 4*(H : ℝ)*((m : ℝ)*L)*t^(H-1) < ε*n := by
      apply (mul_lt_mul_iff_right₀ hs0).mp
      have h1 := mul_le_mul_of_nonneg_left hml (by positivity : 0 ≤ 4*(H : ℝ)*t^(H-1))
      have h2 := mul_lt_mul_of_pos_right hpstrict hn0
      have he : 4*(H : ℝ)*t^(H-1)*(C*A*n*t) = 4*(H : ℝ)*C*A*t^H*n := by
        rw [← hid]
        ring
      rw [he] at h1
      nlinarith
    have hpred : ((H-1 : ℕ) : ℝ) ≤ H := by exact_mod_cast (Nat.sub_le H 1)
    have hcost : (((H-1)*(m*L) : ℕ) : ℝ) ≤ (H : ℝ)*((m : ℝ)*L) := by
      push_cast
      exact mul_le_mul_of_nonneg_right hpred (by positivity)
    change (((H-1)*(m*L) : ℕ) : ℝ) < ε*n*(1/t)^(H-1)/4
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_div]
    apply (lt_div_iff₀ (by positivity : 0 < t^(H-1)*4)).mpr
    have hh := mul_le_mul_of_nonneg_right hcost (by positivity : 0 ≤ 4*t^(H-1))
    nlinarith

/-- The ceiling-logarithm size bound for the dominating sets is uniformly
O(log log n) for all part-size bounds K <= C sqrt(log n). -/
theorem domination_size_bound {ε C : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ K : ℕ,
      1 ≤ K → (K : ℝ) ≤ C*sqrt (log (n : ℝ)) →
      ((⌈log (K : ℝ)/(-log (1-ε/8))⌉₊+1 : ℕ) : ℝ) ≤ A*log (log (n : ℝ)) := by
  let d := -log (1-ε/8)
  have hd : 0 < d := neg_pos.mpr (log_neg (by linarith) (by linarith))
  let A := 2/d+2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  have ht := (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop
    (max 1 (log C))
  have hL := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [ht,hL] with n ht hL
  intro K hK hKC
  change max 1 (log C) ≤ log (log (n : ℝ)) at ht
  change 1 ≤ log (n : ℝ) at hL
  have ht1 := (le_max_left _ _).trans ht
  have htC := (le_max_right _ _).trans ht
  have hLpos : 0 < log (n : ℝ) := by linarith
  have hroot : sqrt (log (n : ℝ)) ≤ log (n : ℝ) := by
    nlinarith [sq_sqrt hLpos.le,sqrt_nonneg (log (n : ℝ))]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hklog := log_le_log hKpos (hKC.trans (mul_le_mul_of_nonneg_left hroot hC.le))
  rw [log_mul hC.ne' hLpos.ne'] at hklog
  have hklog2 : log (K : ℝ) ≤ 2*log (log (n : ℝ)) := by linarith
  have hceil := Nat.ceil_lt_add_one (div_nonneg (log_natCast_nonneg K) hd.le)
  change (⌈log (K : ℝ)/d⌉₊ : ℝ) < log (K : ℝ)/d+1 at hceil
  have hdiv := div_le_div_of_nonneg_right hklog2 hd.le
  have hdivEq : 2*log (log (n : ℝ))/d = (2/d)*log (log (n : ℝ)) := by ring
  rw [hdivEq] at hdiv
  change (⌈log (K : ℝ)/d⌉₊+1 : ℕ) ≤ A*log (log (n : ℝ))
  push_cast
  dsimp [A]
  nlinarith

/-- Both budgets with the exact logarithmic ceiling used in the manuscript,
uniformly over the admissible number of parts and maximum part size. -/
theorem eventually_reservoir_allocation_budgets {ε C : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < C) (H : ℕ) (hH : 1 ≤ H) :
    ∀ᶠ n : ℕ in atTop, ∀ m K : ℕ, 1 ≤ K →
      (K : ℝ) ≤ C*sqrt (log (n : ℝ)) →
      (m : ℝ) ≤ C*n/sqrt (log (n : ℝ)) →
      let L := ⌈log (K : ℝ)/(-log (1-ε/8))⌉₊+1
      let r := 1/log (log (n : ℝ))
      (m : ℝ)*L ≤ ε*r*n/4 ∧
        (((H-1)*(m*L) : ℕ) : ℝ) < ε*n*r^(H-1)/4 := by
  obtain ⟨A,hA,hsize⟩ := domination_size_bound hε hε1 hC
  have hb := eventually_allocation_budgets hε hC hA H hH
  filter_upwards [hsize,hb] with n hn hb
  intro m K hK hKC hm
  exact hb m _ hm (hn K hK hKC)

end HadwigerRamsey.ThomasonUpper
