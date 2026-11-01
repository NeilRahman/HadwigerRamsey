import Mathlib
open scoped Topology
open Real Filter
namespace HadwigerRamsey.Existence

/-- The half-order logarithmic correction, uniformly for large halves. -/
theorem eventually_half_scale {eta d : ℝ} (heta : 0 < eta) (hd : 0 ≤ d) (hdeta : d < eta) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 0 < sqrt (log (m : ℝ)) ∧
      (1+d)*sqrt (log (2*(m : ℝ))) ≤ (1+eta)*sqrt (log (m : ℝ)) := by
  let g := (1+eta)^2-(1+d)^2
  have hg : 0 < g := by dsimp [g]; nlinarith only [heta,hd,hdeta]
  have hl := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 ((1+d)^2*log 2/g))
  filter_upwards [hl,eventually_ge_atTop 2] with m hl hm
  change max 1 ((1+d)^2*log 2/g) ≤ log (m : ℝ) at hl
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hlog : 1 ≤ log (m : ℝ) := (le_max_left _ _).trans hl
  have hcost := (div_le_iff₀ hg).mp ((le_max_right _ _).trans hl)
  have hl2 : log (2*(m : ℝ)) = log 2+log (m : ℝ) := log_mul (by norm_num) hmR.ne'
  have hl2pos : 0 ≤ log (2*(m : ℝ)) := by rw [hl2]; linarith [log_pos (by norm_num : (1:ℝ)<2)]
  refine ⟨hmpos,sqrt_pos.mpr (by linarith),?_⟩
  have hsq : ((1+d)*sqrt (log (2*(m : ℝ))))^2 ≤ ((1+eta)*sqrt (log (m : ℝ)))^2 := by
    rw [mul_pow,mul_pow,sq_sqrt hl2pos,sq_sqrt (by linarith)]
    rw [hl2]
    dsimp only [g] at hcost
    nlinarith only [hcost]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
end HadwigerRamsey.Existence
