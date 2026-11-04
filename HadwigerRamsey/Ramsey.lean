import HadwigerRamsey.Ramsey.Bounds

open Filter Real
open scoped Topology Classical

namespace HadwigerRamsey

/-- Theorem 1.1: the asymptotic three-colour Hadwiger--Ramsey number. -/
theorem theorem1_1 :
    Filter.Tendsto
      (fun k : ℕ => (hadwigerRamsey k : ℝ) /
        ((k : ℝ) * Real.sqrt (Real.log (k : ℝ))))
      Filter.atTop (nhds beta⁻¹) := by
  change Tendsto (fun k : ℕ => (hadwigerRamsey k : ℝ) / Ramsey.scale k)
    atTop (𝓝 beta⁻¹)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c,hc,hcb⟩ := exists_between (show max a 0 < beta⁻¹ by
      exact max_lt ha (inv_pos.mpr beta_pos))
    have hc0 : 0 < c := (le_max_right a 0).trans_lt hc
    have hac : a < c := (le_max_left a 0).trans_lt hc
    have hv := (tendsto_order.mp (Ramsey.floorOrder_ratio hc0)).1 a hac
    filter_upwards [Ramsey.eventually_floor_lt_ramsey hc0 hcb, hv,
      Ramsey.scale_atTop.eventually_gt_atTop 0] with k hk hv hs
    exact hv.trans_le (div_le_div_of_nonneg_right
      (by exact_mod_cast hk.le) hs.le)
  · intro a ha
    obtain ⟨c,hbc,hca⟩ := exists_between ha
    have hc0 : 0 < c := (inv_pos.mpr beta_pos).trans hbc
    have hv := (tendsto_order.mp (Ramsey.ceilOrder_ratio hc0)).2 a hca
    filter_upwards [Ramsey.eventually_ramsey_le_ceil hbc, hv,
      Ramsey.scale_atTop.eventually_gt_atTop 0] with k hk hv hs
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hk) hs.le).trans_lt hv

end HadwigerRamsey
