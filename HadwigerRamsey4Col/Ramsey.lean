import HadwigerRamsey.Existence.MinorTools
import HadwigerRamsey.Ramsey.Scaling

open Filter Real
open scoped Topology Classical

namespace HadwigerRamsey4Col

open HadwigerRamsey

/-- Every edge of the complete graph has exactly one of the `r` colours. -/
def IsDecomposition {r n : ℕ} (G : Fin r → SimpleGraph (Fin n)) : Prop :=
  ∀ u v, u ≠ v → ∃! c, (G c).Adj u v

lemma IsDecomposition.comap {r n m : ℕ} {G : Fin r → SimpleGraph (Fin n)}
    (hG : IsDecomposition G) (f : Fin m → Fin n) (hf : Function.Injective f) :
    IsDecomposition (fun c => (G c).comap f) := by
  intro u v huv
  exact hG (f u) (f v) (hf.ne huv)

/-- All `r`-colourings of the complete graph on `n` vertices force a
monochromatic clique minor of order `k`. -/
def ForcesMinor (r n k : ℕ) : Prop :=
  ∀ G : Fin r → SimpleGraph (Fin n), IsDecomposition G →
    ∃ c : Fin r, HasCliqueMinor (G c) k

lemma forcesMinor_mono {r m n k : ℕ} (hmn : m ≤ n)
    (hm : ForcesMinor r m k) : ForcesMinor r n k := by
  intro G hG
  let f : Fin m → Fin n := Fin.castLE hmn
  have hf : Function.Injective f := Fin.castLE_injective hmn
  obtain ⟨c, hc⟩ := hm (fun c => (G c).comap f) (hG.comap f hf)
  exact ⟨c, hc.map_injective ⟨f, fun h => h⟩ hf⟩

/-- The least order forcing a monochromatic `K_k` minor. The existence of
such an order follows below from the transfer bound. -/
noncomputable def hadwigerRamsey (r k : ℕ) : ℕ := sInf {n | ForcesMinor r n k}

/-- The precise eventual bound asserted by Theorem 3, with a named constant. -/
def TransferBound (r : ℕ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ G : Fin r → SimpleGraph (Fin n), IsDecomposition G →
      ∃ c : Fin r, (b - ε) * n / sqrt (log (n : ℝ)) ≤ hadwigerNumber (G c)

/-- The precise eventual bound asserted by Theorem 4, with a named constant. -/
def ConstructionBound (r : ℕ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ G : Fin r → SimpleGraph (Fin n), IsDecomposition G ∧
      ∀ c : Fin r, (hadwigerNumber (G c) : ℝ) ≤ (b + ε) * n / sqrt (log (n : ℝ))

namespace Ramsey

open HadwigerRamsey.Ramsey

lemma order_div_sqrt_log_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) / sqrt (log (n : ℝ))) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 < sqrt (log (n : ℝ)) := sqrt_pos.mpr (log_pos hnR)
  apply (le_div_iff₀ hs).mpr
  calc
    sqrt (n : ℝ) * sqrt (log (n : ℝ)) ≤ sqrt (n : ℝ) * sqrt (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      apply sqrt_le_sqrt
      linarith only [log_le_sub_one_of_pos (show (0 : ℝ) < n by positivity)]
    _ = n := mul_self_sqrt (Nat.cast_nonneg n)

lemma forcesMinor_exists {r : ℕ} {b : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (k : ℕ) : ∃ n, ForcesMinor r n k := by
  have ht : Tendsto (fun n : ℕ => (b - b / 2) * n / sqrt (log (n : ℝ)))
      atTop atTop := by
    simpa only [mul_div_assoc] using order_div_sqrt_log_atTop.const_mul_atTop
      (show 0 < b - b / 2 by linarith)
  obtain ⟨n, hn, hk⟩ := ((hT (b / 2) (by positivity)).and
    (ht.eventually_ge_atTop (k : ℝ))).exists
  refine ⟨n, fun G hG => ?_⟩
  obtain ⟨c, hc⟩ := hn G hG
  refine ⟨c, (hasCliqueMinor_iff_le_hadwigerNumber (G c)).mpr ?_⟩
  exact_mod_cast hk.trans hc

end Ramsey

lemma hadwigerRamsey_spec {r : ℕ} {b : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (k : ℕ) : ForcesMinor r (hadwigerRamsey r k) k :=
  Nat.sInf_mem (Ramsey.forcesMinor_exists hb hT k)

lemma hadwigerRamsey_le {r n k : ℕ} (h : ForcesMinor r n k) :
    hadwigerRamsey r k ≤ n := Nat.sInf_le h

lemma hadwigerRamsey_le_iff {r : ℕ} {b : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (n k : ℕ) :
    hadwigerRamsey r k ≤ n ↔ ForcesMinor r n k :=
  ⟨fun h => forcesMinor_mono h (hadwigerRamsey_spec hb hT k), hadwigerRamsey_le⟩

lemma lt_hadwigerRamsey {r n k : ℕ} {b : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (G : Fin r → SimpleGraph (Fin n))
    (hG : IsDecomposition G) (hk : ∀ c, hadwigerNumber (G c) < k) :
    n < hadwigerRamsey r k := by
  by_contra h
  obtain ⟨c, hc⟩ := (hadwigerRamsey_le_iff hb hT n k).mp (by omega) G hG
  exact (not_le_of_gt (hk c)) (cliqueMinor_le_hadwigerNumber hc)

namespace Ramsey

open HadwigerRamsey.Ramsey

lemma eventually_floor_lt_ramsey {r : ℕ} {b c : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (hC : ConstructionBound r b)
    (hc : 0 < c) (hcb : c < b⁻¹) :
    ∀ᶠ k : ℕ in atTop, floorOrder c k < hadwigerRamsey r k := by
  have hbc1 : b * c < 1 := by
    have hh := (lt_div_iff₀ hb).mp (show c < 1 / b by simpa using hcb)
    nlinarith only [hh]
  let ε := (1 - b * c) / (2 * c)
  have hε : 0 < ε := div_pos (sub_pos.mpr hbc1) (by positivity)
  have hεeq : ε * (2 * c) = 1 - b * c := div_mul_cancel₀ _ (by positivity)
  have hcoef : (b + ε) * c < 1 := by nlinarith only [hεeq, hbc1]
  have ht := (floorOrder_inverse_limit hc).const_mul (b + ε)
  have hv := (tendsto_order.mp ht).2 1 hcoef
  filter_upwards [(floorOrder_atTop hc).eventually (hC ε hε), hv,
    (eventually_ge_atTop 1 : ∀ᶠ k : ℕ in atTop, 1 ≤ k)] with k hn hk hkpos
  obtain ⟨G, hG, hGi⟩ := hn
  apply lt_hadwigerRamsey hb hT G hG
  intro i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hh : (b + ε) * (floorOrder c k : ℝ) / sqrt (log (floorOrder c k : ℝ)) < k := by
    have hh : ((b + ε) * (floorOrder c k : ℝ) / sqrt (log (floorOrder c k : ℝ))) /
        (k : ℝ) < 1 := by simpa only [mul_div_assoc] using hk
    simpa only [one_mul] using (div_lt_iff₀ hkR).mp hh
  exact_mod_cast (hGi i).trans_lt hh

lemma eventually_ramsey_le_ceil {r : ℕ} {b c : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (hcb : b⁻¹ < c) :
    ∀ᶠ k : ℕ in atTop, hadwigerRamsey r k ≤ ceilOrder c k := by
  have hc : 0 < c := (inv_pos.mpr hb).trans hcb
  have hbc1 : 1 < b * c := by
    have hh := (div_lt_iff₀ hb).mp (show 1 / b < c by simpa using hcb)
    nlinarith only [hh]
  let ε := (b * c - 1) / (2 * c)
  have hε : 0 < ε := div_pos (sub_pos.mpr hbc1) (by positivity)
  have hεeq : ε * (2 * c) = b * c - 1 := div_mul_cancel₀ _ (by positivity)
  have hcoef : 1 < (b - ε) * c := by nlinarith only [hεeq, hbc1]
  have ht := (ceilOrder_inverse_limit hc).const_mul (b - ε)
  have hv := (tendsto_order.mp ht).1 1 hcoef
  filter_upwards [(ceilOrder_atTop hc).eventually (hT ε hε), hv,
    (eventually_ge_atTop 1 : ∀ᶠ k : ℕ in atTop, 1 ≤ k)] with k hn hk hkpos
  apply hadwigerRamsey_le
  intro G hG
  obtain ⟨i, hi⟩ := hn G hG
  refine ⟨i, (hasCliqueMinor_iff_le_hadwigerNumber (G i)).mpr ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hh : (k : ℝ) < (b - ε) * (ceilOrder c k : ℝ) / sqrt (log (ceilOrder c k : ℝ)) := by
    have hh : 1 < ((b - ε) * (ceilOrder c k : ℝ) / sqrt (log (ceilOrder c k : ℝ))) /
        (k : ℝ) := by simpa only [mul_div_assoc] using hk
    simpa only [one_mul] using (lt_div_iff₀ hkR).mp hh
  exact_mod_cast (hh.trans_le hi).le

end Ramsey

/-- Asymptotic inversion: the transfer and construction bounds imply the
Hadwiger--Ramsey limit with the reciprocal leading constant. -/
theorem ramsey_asymptotic_of_bounds {r : ℕ} {b : ℝ} (hb : 0 < b)
    (hT : TransferBound r b) (hC : ConstructionBound r b) :
    Tendsto (fun k : ℕ => (hadwigerRamsey r k : ℝ) /
      ((k : ℝ) * sqrt (log (k : ℝ)))) atTop (𝓝 b⁻¹) := by
  change Tendsto (fun k : ℕ => (hadwigerRamsey r k : ℝ) / HadwigerRamsey.Ramsey.scale k)
    atTop (𝓝 b⁻¹)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c, hc, hcb⟩ := exists_between (show max a 0 < b⁻¹ by
      exact max_lt ha (inv_pos.mpr hb))
    have hc0 : 0 < c := (le_max_right a 0).trans_lt hc
    have hac : a < c := (le_max_left a 0).trans_lt hc
    have hv := (tendsto_order.mp (HadwigerRamsey.Ramsey.floorOrder_ratio hc0)).1 a hac
    filter_upwards [Ramsey.eventually_floor_lt_ramsey hb hT hC hc0 hcb, hv,
      HadwigerRamsey.Ramsey.scale_atTop.eventually_gt_atTop 0] with k hk hv hs
    exact hv.trans_le (div_le_div_of_nonneg_right
      (by exact_mod_cast hk.le) hs.le)
  · intro a ha
    obtain ⟨c, hbc, hca⟩ := exists_between ha
    have hc0 : 0 < c := (inv_pos.mpr hb).trans hbc
    have hv := (tendsto_order.mp (HadwigerRamsey.Ramsey.ceilOrder_ratio hc0)).2 a hca
    filter_upwards [Ramsey.eventually_ramsey_le_ceil hb hT hbc, hv,
      HadwigerRamsey.Ramsey.scale_atTop.eventually_gt_atTop 0] with k hk hv hs
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hk) hs.le).trans_lt hv

end HadwigerRamsey4Col
