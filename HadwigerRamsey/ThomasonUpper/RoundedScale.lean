import HadwigerRamsey.Asymptotic

open scoped BigOperators Topology
open Real Filter

namespace HadwigerRamsey.ThomasonUpper

/-- Uniform bounds for the ceiling square-root-logarithmic scale in A.3.
It grows past every fixed threshold and is negligible relative to n,
uniformly for entropy in a fixed positive compact interval. -/
theorem eventually_rounded_scale {lambda B gamma A d : ℝ}
    (hlambda : 0 < lambda) (hB : 0 < B) (hgamma : 0 ≤ gamma)
    (hA : 0 < A) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ Lambda : ℝ, lambda ≤ Lambda → Lambda ≤ B →
      let L := ⌈(1+gamma)*sqrt (log (n : ℝ)/Lambda)⌉₊
      0 < L ∧ A ≤ (L : ℝ) ∧
      (L : ℝ) ≤ ((1+gamma)/sqrt lambda+1)*sqrt (log (n : ℝ)) ∧
      (L : ℝ)/(n : ℝ) ≤ d ∧
      (1+gamma)*sqrt (log (n : ℝ)/Lambda) ≤ (L : ℝ) := by
  let C := (1+gamma)/sqrt lambda+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have ht : Tendsto (fun n : ℕ => sqrt (log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hg := eventually_log_power_le (1/2) 1 (d/C) (by norm_num) (div_pos hd hC)
  filter_upwards [ht.eventually_ge_atTop (max 1 (A*sqrt B/(1+gamma))),hg,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    (eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hroot hpower hlog hn
  change 1 ≤ log (n : ℝ) at hlog
  intro Lambda hlo hhi
  let L := ⌈(1+gamma)*sqrt (log (n : ℝ)/Lambda)⌉₊
  have hLambda : 0 < Lambda := hlambda.trans_le hlo
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hroot1 : 1 ≤ sqrt (log (n : ℝ)) := (le_max_left _ _).trans hroot
  have hrootA : A*sqrt B/(1+gamma) ≤ sqrt (log (n : ℝ)) := (le_max_right _ _).trans hroot
  have hsqLambda : 0 < sqrt Lambda := sqrt_pos.mpr hLambda
  have hsqlambda : 0 < sqrt lambda := sqrt_pos.mpr hlambda
  have hsqB : 0 < sqrt B := sqrt_pos.mpr hB
  have hxnon : 0 ≤ (1+gamma)*sqrt (log (n : ℝ)/Lambda) := by positivity
  have hceil := Nat.le_ceil ((1+gamma)*sqrt (log (n : ℝ)/Lambda))
  change _ ≤ (L : ℝ) at hceil
  have hnext := Nat.ceil_lt_add_one hxnon
  change (L : ℝ) < (1+gamma)*sqrt (log (n : ℝ)/Lambda)+1 at hnext
  have hdiv : sqrt (log (n : ℝ)/Lambda) = sqrt (log (n : ℝ))/sqrt Lambda :=
    sqrt_div (by linarith) Lambda
  have hlower : A ≤ (1+gamma)*sqrt (log (n : ℝ)/Lambda) := by
    rw [hdiv,← mul_div_assoc]
    apply (le_div_iff₀ hsqLambda).mpr
    have hh := (div_le_iff₀ (by linarith : 0 < 1+gamma)).mp hrootA
    have hmono := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hhi) hA.le
    nlinarith
  have hxupper : (1+gamma)*sqrt (log (n : ℝ)/Lambda) ≤
      ((1+gamma)/sqrt lambda)*sqrt (log (n : ℝ)) := by
    rw [hdiv,← mul_div_assoc]
    have hh := div_le_div_of_nonneg_left
      (mul_nonneg (by linarith : 0 ≤ 1+gamma) (sqrt_nonneg (log (n : ℝ)))) hsqlambda (sqrt_le_sqrt hlo)
    calc
      _ ≤ ((1+gamma)*sqrt (log (n : ℝ)))/sqrt lambda := hh
      _ = _ := by ring
  have hupper : (L : ℝ) ≤ C*sqrt (log (n : ℝ)) := by
    dsimp only [C]
    nlinarith
  have hfrac : (L : ℝ)/(n : ℝ) ≤ d := by
    rw [← sqrt_eq_rpow,rpow_one] at hpower
    apply (div_le_iff₀ hnR).mpr
    have hh := mul_le_mul_of_nonneg_left hpower hC.le
    have he : C*((d/C)*(n : ℝ)) = d*n := by field_simp
    rw [he] at hh
    exact hupper.trans hh
  refine ⟨?_,hlower.trans hceil,hupper,hfrac,hceil⟩
  have hpos : (0 : ℝ) < L := hA.trans_le (hlower.trans hceil)
  exact_mod_cast hpos

end HadwigerRamsey.ThomasonUpper
