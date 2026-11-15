import HadwigerRamsey.Weights
import HadwigerRamsey.Analytic

open scoped BigOperators Topology
open Finset Real Filter
set_option maxHeartbeats 2000000
namespace HadwigerRamsey

/-- The finite tail bound, with the combinatorial factor absorbed into an exponential. -/
noncomputable def tailBound (n s : ℕ) (Λ : ℝ) : ℝ :=
  exp ((n : ℝ) * log s - (s : ℝ) * (s - 1) / 2 *
    exp (-((n : ℝ)^2 * Λ) / ((s : ℝ) * (s - 1))))

/-- The only growth input needed below: powers dominate powers of logarithms.
This is a direct reuse of Mathlib's real-power asymptotics. -/
lemma eventually_log_power_le (r γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (log (n : ℝ)) ^ r ≤ c * (n : ℝ)^γ := by
  have h := (isLittleO_log_rpow_rpow_atTop r hγ).bound hc
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with n hn hn1
  have hpos : 0 ≤ (log (n : ℝ))^r := rpow_nonneg (log_natCast_nonneg n) r
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)] using hn

/-- A convenient version which only starts after `n ≥ 1`. -/
lemma eventually_sqrt_log_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, sqrt (log (n : ℝ)) ≤ c * n := by
  have h := eventually_log_power_le (1/2) 1 c (by norm_num) hc
  simpa only [← Real.sqrt_eq_rpow, Real.rpow_one] using h


/-- Uniform asymptotic estimate used after Lemma B.1 to prove Theorem 1.4. -/
theorem uniform_tail_bound (ε B : ℝ) (hε : 0 < ε) (_hB : 0 ≤ B) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ Λ : ℝ, ε^2 ≤ Λ → Λ ≤ B →
      let R := (1+ε) * (n : ℝ) * sqrt Λ / sqrt (log n)
      let s := ⌈R⌉₊
      2 ≤ s ∧ (s : ℝ) ≤ n ∧ tailBound n s Λ ≤ ε := by
  let θ : ℝ := 1 + ε/2
  have hθ : 1 < θ := by dsimp [θ]; linarith
  have hθA : θ < 1+ε := by dsimp [θ]; linarith
  have hθ0 : 0 < θ := by linarith
  have hA : 0 < 1+ε := by linarith
  have hdiff : 0 < (1+ε)^2 - θ^2 := by nlinarith
  let D := max 2 ((1+ε)^2 / ((1+ε)^2 - θ^2))
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD2 : 2 ≤ D := le_max_left _ _
  have hDdiff : (1+ε)^2 ≤ D * ((1+ε)^2 - θ^2) := by
    exact (div_le_iff₀ hdiff).mp (le_max_right _ _)
  let γ := 1 - 1 / θ^2
  have hγ : 0 < γ := by dsimp [γ]; rw [sub_pos, div_lt_one₀ (by positivity)]; nlinarith
  let C := θ^2 * ε^2 / 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hgrowth := eventually_log_power_le 2 γ (C/2) hγ (by positivity)
  have hsmall := eventually_sqrt_log_le ((1+ε)*ε/D) (by positivity)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (4*(1+ε)^2*B))
  have hnlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (-log ε)
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ Λ : ℝ, ε^2 ≤ Λ → Λ ≤ B →
      let R := (1+ε) * (n : ℝ) * sqrt Λ / sqrt (log n)
      let s := ⌈R⌉₊
      2 ≤ s ∧ (s : ℝ) ≤ n ∧ tailBound n s Λ ≤ ε := by
    filter_upwards [hgrowth, hsmall, hlog, hnlog, eventually_ge_atTop 2]
      with n hg hsml hl hnl hn
    intro Λ hΛ hΛB
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl1 : 1 ≤ log (n : ℝ) := (le_max_left _ _).trans hl
    have hl0 : 0 < log (n : ℝ) := by linarith
    have hsq0 : 0 < sqrt (log (n : ℝ)) := sqrt_pos.mpr hl0
    have hΛ0 : 0 ≤ Λ := (sq_nonneg ε).trans hΛ
    have hsqrt : ε ≤ sqrt Λ := by nlinarith [sq_sqrt hΛ0, sqrt_nonneg Λ]
    let R := (1+ε) * (n : ℝ) * sqrt Λ / sqrt (log n)
    let s := ⌈R⌉₊
    have hsqrtpos : 0 < sqrt Λ := hε.trans_le hsqrt
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRD : D ≤ R := by
      apply (le_div_iff₀ hsq0).mpr
      have hh : D * sqrt (log (n : ℝ)) ≤ (1+ε)*ε*n := by
        have hh := mul_le_mul_of_nonneg_left hsml hD.le
        have hd0 : D ≠ 0 := ne_of_gt hD
        field_simp at hh ⊢
        nlinarith
      apply hh.trans
      calc
        (1+ε)*ε*n = ((1+ε)*n)*ε := by ring
        _ ≤ ((1+ε)*n)*sqrt Λ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have hR2 : 2 ≤ R := hD2.trans hRD
    have hupper : 2*(1+ε)*sqrt Λ ≤ sqrt (log (n : ℝ)) := by
      have hlogB : 4*(1+ε)^2*B ≤ log (n : ℝ) := (le_max_right _ _).trans hl
      have hsq := sq_sqrt hl0.le
      have hsqΛ := sq_sqrt hΛ0
      have hsquare : (2*(1+ε)*sqrt Λ)^2 ≤ (sqrt (log (n : ℝ)))^2 := by
        nlinarith only [hsq, hsqΛ, hlogB, mul_le_mul_of_nonneg_left hΛB (show 0 ≤ 4*(1+ε)^2 by positivity)]
      nlinarith only [hsquare, sqrt_nonneg Λ, hsq0, hA]
    have hRupper : R ≤ (n : ℝ)/2 := by
      apply (div_le_iff₀ hsq0).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hupper hn0.le]
    have hsR : R ≤ (s : ℝ) := Nat.le_ceil R
    have hsR1 : (s : ℝ) < R+1 := Nat.ceil_lt_add_one hRpos.le
    have hs2 : 2 ≤ s := by exact_mod_cast (hR2.trans hsR)
    have hsN : (s : ℝ) ≤ n := by linarith
    have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hs1 : 0 < (s : ℝ)-1 := by
      have hh : (2 : ℝ) ≤ s := by exact_mod_cast hs2
      linarith only [hh]
    have hss : 0 < (s : ℝ)*((s : ℝ)-1) := mul_pos hspos hs1
    have hRidentity : R^2 * log (n : ℝ) = (1+ε)^2 * (n : ℝ)^2 * Λ := by
      dsimp [R]
      rw [div_pow, mul_pow, mul_pow, sq_sqrt hΛ0, sq_sqrt hl0.le]
      field_simp
    have hroundR : θ^2 * R^2 ≤ (1+ε)^2 * (R*(R-1)) := by
      have hh := mul_le_mul_of_nonneg_right hRD hdiff.le
      have h := hDdiff.trans hh
      have hhR := mul_le_mul_of_nonneg_right h hRpos.le
      nlinarith only [hhR]
    have hround : θ^2 * (n : ℝ)^2 * Λ ≤ log (n : ℝ) * ((s : ℝ)*((s : ℝ)-1)) := by
      have hmul : R*(R-1) ≤ (s : ℝ)*((s : ℝ)-1) := by
        have hh := mul_le_mul hsR (show R-1 ≤ (s : ℝ)-1 by linarith) (by linarith) (by positivity)
        exact hh
      have hh := mul_le_mul_of_nonneg_right hroundR hl0.le
      have hhh := mul_le_mul_of_nonneg_left hmul (sq_nonneg (1+ε))
      have hscaled : (1+ε)^2 * (θ^2*(n : ℝ)^2*Λ) ≤
          (1+ε)^2 * (log (n : ℝ)*((s : ℝ)*((s : ℝ)-1))) := by
        calc
          _ = θ^2 * ((1+ε)^2 * (n : ℝ)^2 * Λ) := by ring
          _ = θ^2 * (R^2 * log (n : ℝ)) := by rw [hRidentity]
          _ = θ^2 * R^2 * log (n : ℝ) := by ring
          _ ≤ (1+ε)^2*(R*(R-1))*log (n : ℝ) := hh
          _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hhh hl0.le]
      exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hA)).mp hscaled
    have hratio : (n : ℝ)^2*Λ / ((s : ℝ)*((s : ℝ)-1)) ≤ log (n : ℝ)/θ^2 := by
      apply (div_le_div_iff₀ hss (sq_pos_of_pos hθ0)).mpr
      nlinarith only [hround]
    have hM : θ^2 * (n : ℝ)^2 * Λ / (2*log (n : ℝ)) ≤ (s : ℝ)*((s : ℝ)-1)/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2*log (n : ℝ))).mpr
      nlinarith only [hround]
    have hMε : C * (n : ℝ)^2 / log (n : ℝ) ≤ (s : ℝ)*((s : ℝ)-1)/2 := by
      apply le_trans _ hM
      dsimp [C]
      calc
        θ^2*ε^2/2*(n : ℝ)^2/log (n : ℝ) = θ^2*(n : ℝ)^2*ε^2/(2*log (n : ℝ)) := by ring
        _ ≤ _ := by gcongr
    have hexp : (n : ℝ)^2 * exp (-log (n : ℝ)/θ^2) = (n : ℝ)*(n : ℝ)^γ := by
      rw [rpow_def_of_pos hn0]
      calc
        _ = exp (2*log (n : ℝ)) * exp (-log (n : ℝ)/θ^2) := by rw [show (2 : ℝ)*log (n : ℝ) = log (n : ℝ)+log (n : ℝ) by ring, exp_add, exp_log hn0]; ring
        _ = exp (log (n : ℝ) + log (n : ℝ)*γ) := by rw [← exp_add]; congr 1; dsimp [γ]; ring
        _ = _ := by rw [exp_add, exp_log hn0]
    have hpenalty : 2*(n : ℝ)*log (n : ℝ) ≤
        (s : ℝ)*((s : ℝ)-1)/2 * exp (-((n : ℝ)^2*Λ)/((s : ℝ)*((s : ℝ)-1))) := by
      have hgg : 2*log (n : ℝ)^2 ≤ C*(n : ℝ)^γ := by
        rw [Real.rpow_two] at hg
        linarith
      calc
        _ ≤ C * ((n : ℝ)*(n : ℝ)^γ) / log (n : ℝ) := by
          apply (le_div_iff₀ hl0).mpr
          nlinarith only [mul_le_mul_of_nonneg_left hgg hn0.le]
        _ = C*(n : ℝ)^2/log (n : ℝ) * exp (-log (n : ℝ)/θ^2) := by rw [← hexp]; ring
        _ ≤ _ := mul_le_mul hMε (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hratio))
          (by positivity) (by positivity)
    have hlogs : log (s : ℝ) ≤ log (n : ℝ) := Real.log_le_log hspos hsN
    refine ⟨hs2, hsN, ?_⟩
    apply (Real.exp_le_exp.mpr (show
      (n : ℝ)*log (s : ℝ) - (s : ℝ)*((s : ℝ)-1)/2 *
        exp (-((n : ℝ)^2*Λ)/((s : ℝ)*((s : ℝ)-1))) ≤ log ε from ?_)).trans_eq (exp_log hε)
    have hh := mul_le_mul_of_nonneg_left hlogs hn0.le
    have hnn : log (n : ℝ) ≤ (n : ℝ)*log (n : ℝ) := by nlinarith
    simp only [Function.comp_def] at hnl
    linarith only [hh, hpenalty, hnn, hnl]
  exact eventually_atTop.mp hevent

end HadwigerRamsey
