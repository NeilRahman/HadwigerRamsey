import Mathlib

open scoped BigOperators Topology
open Filter Real

namespace HadwigerRamsey4Col
namespace Construction

/-- A positive limiting fraction of the vertices tends to infinity. -/
lemma componentOrder_atTop {N : ℕ → ℕ} {s : ℝ} (hs : 0 < s)
    (h : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto N atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have ht := h.pos_mul_atTop hs (tendsto_natCast_atTop_atTop (R := ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast (by omega : n ≠ 0))

/-- A component of asymptotically positive relative size has the same logarithmic scale. -/
lemma component_log_ratio {N : ℕ → ℕ} {s : ℝ} (hs : 0 < s)
    (h : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => log (N n : ℝ) / log (n : ℝ)) atTop (𝓝 1) := by
  have hlog := (h.log hs.ne').div_atTop
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have ht : Tendsto (fun n : ℕ => log ((N n : ℝ) / n) / log (n : ℝ) + 1)
      atTop (𝓝 1) := by simpa using hlog.add_const 1
  apply ht.congr'
  filter_upwards [(componentOrder_atTop hs h).eventually_ge_atTop 1,
    (eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hN hn
  have hNp : (0 : ℝ) < N n := by exact_mod_cast hN
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hn)).ne'
  rw [log_div hNp.ne' hnp.ne', sub_div, div_self hnl]
  ring

lemma component_sqrt_log_ratio {N : ℕ → ℕ} {s : ℝ} (hs : 0 < s)
    (h : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => sqrt (log (n : ℝ) / log (N n : ℝ))) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one, sqrt_one] using
    ((component_log_ratio hs h).inv₀ (by norm_num : (1 : ℝ) ≠ 0)).sqrt

/-- Every finite component entropy is continuous in its vertex masses. -/
lemma component_entropy_limit {ι : Type*} [Fintype ι] (S : Finset ι)
    (a : ℕ → ι → ℝ) (α : ι → ℝ) (p : ι → ι → ℝ)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (α i))) :
    Tendsto (fun n => sqrt (∑ i ∈ S, ∑ j ∈ S,
      a n i * a n j * (-log (1 - p i j)))) atTop
      (𝓝 (sqrt (∑ i ∈ S, ∑ j ∈ S, α i * α j * (-log (1 - p i j))))) := by
  apply Tendsto.sqrt
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((ha i).mul (ha j)).mul_const _

/-- The random-minor bound on a component has the expected ambient normalization. -/
lemma component_bound_limit {N : ℕ → ℕ} {s E δ : ℝ} (hs : 0 < s)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (𝓝 s))
    {energy : ℕ → ℝ} (hE : Tendsto energy atTop (𝓝 E)) :
    Tendsto (fun n => (1 + δ) * energy n * sqrt (log (n : ℝ) / log (N n : ℝ)))
      atTop (𝓝 ((1 + δ) * E)) := by
  simpa only [mul_one] using (hE.const_mul (1 + δ)).mul (component_sqrt_log_ratio hs hN)

end Construction
end HadwigerRamsey4Col
