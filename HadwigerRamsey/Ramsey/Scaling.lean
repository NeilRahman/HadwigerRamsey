import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Sqrt

open scoped Topology
open Real Filter

namespace HadwigerRamsey.Ramsey

/-- The scale on the right side of the Hadwiger--Ramsey asymptotic. -/
noncomputable def scale (k : ℕ) : ℝ := (k : ℝ) * sqrt (log (k : ℝ))

theorem scale_atTop : Tendsto scale atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
    (tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- A sequence asymptotic to a positive multiple of the Ramsey scale is unbounded. -/
theorem order_atTop {n : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun k => (n k : ℝ) / scale k) atTop (𝓝 c)) :
    Tendsto n atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have ht := h.pos_mul_atTop hc scale_atTop
  apply ht.congr'
  filter_upwards [scale_atTop.eventually_gt_atTop 0] with k hk
  exact div_mul_cancel₀ _ hk.ne'

/-- Replacing k by a positive multiple of k sqrt(log k) changes log k by a factor
tending to one. -/
theorem log_order_ratio {n : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun k => (n k : ℝ) / scale k) atTop (𝓝 c)) :
    Tendsto (fun k => log (n k : ℝ) / log (k : ℝ)) atTop (𝓝 1) := by
  have hklog : Tendsto (fun k : ℕ => log (k : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfirst := (h.log hc.ne').div_atTop hklog
  have hsecond := isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hklog
  have ht' : Tendsto (fun k : ℕ =>
      log ((n k : ℝ) / scale k) / log (k : ℝ) + 1 +
        (log (log (k : ℝ)) / log (k : ℝ)) / 2) atTop (𝓝 1) := by
    simpa using (hfirst.add (tendsto_const_nhds (x := (1 : ℝ)))).add
      (hsecond.div_const 2)
  apply ht'.congr'
  filter_upwards [(order_atTop hc h).eventually_ge_atTop 1,
    (eventually_ge_atTop 2 : ∀ᶠ k : ℕ in atTop, 2 ≤ k)] with k hn hk
  have hnp : (0 : ℝ) < n k := by exact_mod_cast hn
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkl : 0 < log (k : ℝ) := log_pos (by exact_mod_cast hk)
  have hroot : 0 < sqrt (log (k : ℝ)) := sqrt_pos.mpr hkl
  rw [scale, log_div hnp.ne' (mul_ne_zero hkp.ne' hroot.ne'),
    log_mul hkp.ne' hroot.ne', log_sqrt hkl.le]
  field_simp [hkl.ne']
  ring

/-- The inverse scale recovers the same positive leading coefficient. -/
theorem inverse_scale_limit {n : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun k => (n k : ℝ) / scale k) atTop (𝓝 c)) :
    Tendsto (fun k => (n k : ℝ) / sqrt (log (n k : ℝ)) / (k : ℝ))
      atTop (𝓝 c) := by
  have hlogs := (log_order_ratio hc h).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hroots := hlogs.sqrt
  have ht : Tendsto (fun k => ((n k : ℝ) / scale k) *
      sqrt ((log (n k : ℝ) / log (k : ℝ))⁻¹)) atTop (𝓝 c) := by
    simpa using h.mul hroots
  apply ht.congr'
  filter_upwards [(eventually_ge_atTop 2 : ∀ᶠ k : ℕ in atTop, 2 ≤ k)] with k hk
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkl : 0 < log (k : ℝ) := log_pos (by exact_mod_cast hk)
  have hroot : 0 < sqrt (log (k : ℝ)) := sqrt_pos.mpr hkl
  rw [inv_div, sqrt_div hkl.le, scale]
  field_simp

noncomputable def floorOrder (c : ℝ) (k : ℕ) : ℕ := ⌊c * scale k⌋₊
noncomputable def ceilOrder (c : ℝ) (k : ℕ) : ℕ := ⌈c * scale k⌉₊

theorem floorOrder_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => (floorOrder c k : ℝ) / scale k) atTop (𝓝 c) :=
  (tendsto_nat_floor_mul_div_atTop hc.le).comp scale_atTop

theorem ceilOrder_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => (ceilOrder c k : ℝ) / scale k) atTop (𝓝 c) :=
  (tendsto_nat_ceil_mul_div_atTop hc.le).comp scale_atTop

theorem floorOrder_atTop {c : ℝ} (hc : 0 < c) : Tendsto (floorOrder c) atTop atTop :=
  order_atTop hc (floorOrder_ratio hc)

theorem ceilOrder_atTop {c : ℝ} (hc : 0 < c) : Tendsto (ceilOrder c) atTop atTop :=
  order_atTop hc (ceilOrder_ratio hc)

theorem floorOrder_inverse_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => (floorOrder c k : ℝ) /
      sqrt (log (floorOrder c k : ℝ)) / (k : ℝ)) atTop (𝓝 c) :=
  inverse_scale_limit hc (floorOrder_ratio hc)

theorem ceilOrder_inverse_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => (ceilOrder c k : ℝ) /
      sqrt (log (ceilOrder c k : ℝ)) / (k : ℝ)) atTop (𝓝 c) :=
  inverse_scale_limit hc (ceilOrder_ratio hc)

end HadwigerRamsey.Ramsey
