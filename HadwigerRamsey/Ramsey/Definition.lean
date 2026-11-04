import HadwigerRamsey.Main
import HadwigerRamsey.Existence

open Filter Real
open scoped Topology Classical

namespace HadwigerRamsey

/-- Every three-colouring of the complete graph on `n` vertices has a
monochromatic complete minor of order `k`. -/
def ForcesMinor (n k : ℕ) : Prop :=
  ∀ G : Fin 3 → SimpleGraph (Fin n), IsThreeDecomposition G →
    ∃ i : Fin 3, HasCliqueMinor (G i) k

namespace Ramsey

lemma forcesMinor_mono {m n k : ℕ} (hmn : m ≤ n)
    (hm : ForcesMinor m k) : ForcesMinor n k := by
  intro G hG
  let f : Fin m → Fin n := Fin.castLE hmn
  have hf : Function.Injective f := Fin.castLE_injective hmn
  obtain ⟨i, hi⟩ := hm (fun i => (G i).comap f) (hG.comap f hf)
  exact ⟨i, hi.map_injective ⟨f, fun h => h⟩ hf⟩

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

/-- Theorem 1.3 supplies a finite forcing order for every minor order. -/
lemma forcesMinor_exists (k : ℕ) : ∃ n, ForcesMinor n k := by
  obtain ⟨N, hN⟩ := mainthm (1/2) (by norm_num)
  have ht : Tendsto (fun n : ℕ => (1-(1/2 : ℝ))*beta*n/sqrt (log (n : ℝ)))
      atTop atTop := by
    have hh := order_div_sqrt_log_atTop.const_mul_atTop (show 0 < (1-(1/2 : ℝ))*beta by
      have := beta_pos; positivity)
    simpa only [mul_div_assoc] using hh
  obtain ⟨n, hn, hk⟩ := ((eventually_ge_atTop N).and (ht.eventually_ge_atTop (k : ℝ))).exists
  refine ⟨n, fun G hG => ?_⟩
  obtain ⟨i, hi⟩ := hN n hn G hG
  refine ⟨i, (hasCliqueMinor_iff_le_hadwigerNumber (G i)).mpr ?_⟩
  exact_mod_cast hk.trans hi

end Ramsey

/-- The three-colour Hadwiger--Ramsey number: the least forcing order. -/
noncomputable def hadwigerRamsey (k : ℕ) : ℕ := Nat.find (Ramsey.forcesMinor_exists k)

theorem hadwigerRamsey_spec (k : ℕ) : ForcesMinor (hadwigerRamsey k) k :=
  Nat.find_spec (Ramsey.forcesMinor_exists k)

theorem hadwigerRamsey_le {n k : ℕ} (h : ForcesMinor n k) : hadwigerRamsey k ≤ n :=
  Nat.find_min' (Ramsey.forcesMinor_exists k) h

theorem hadwigerRamsey_le_iff (n k : ℕ) : hadwigerRamsey k ≤ n ↔ ForcesMinor n k :=
  ⟨fun h => Ramsey.forcesMinor_mono h (hadwigerRamsey_spec k), hadwigerRamsey_le⟩

theorem lt_hadwigerRamsey {n k : ℕ} (G : Fin 3 → SimpleGraph (Fin n))
    (hG : IsThreeDecomposition G) (hk : ∀ i, hadwigerNumber (G i) < k) :
    n < hadwigerRamsey k := by
  by_contra h
  obtain ⟨i, hi⟩ := (hadwigerRamsey_le_iff n k).mp (by omega) G hG
  exact (not_le_of_gt (hk i)) (cliqueMinor_le_hadwigerNumber hi)

end HadwigerRamsey
