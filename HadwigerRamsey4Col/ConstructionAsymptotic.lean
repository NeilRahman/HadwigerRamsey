import HadwigerRamsey4Col.ComponentProgram
import HadwigerRamsey4Col.ConstructionPartition
import HadwigerRamsey4Col.ConstructionLimits
import HadwigerRamsey.Blocks

open scoped BigOperators Topology Classical
open Filter Real HadwigerRamsey Finset

namespace HadwigerRamsey4Col
namespace Construction

lemma partMass_pos_of_energy_pos {r : ℕ} (I : ComponentInstance r)
    (c : Fin r) (t : Fin I.k) (hE : 0 < I.energy c t) : 0 < I.partMass c t := by
  have hne : (univ.filter (fun i => I.label c i = t)).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [ComponentInstance.energy, ComponentInstance.partEntropy, he] at hE
  exact sum_pos (fun i _ => I.mass_pos i) hne

lemma partMass_le_one {r : ℕ} (I : ComponentInstance r)
    (c : Fin r) (t : Fin I.k) : I.partMass c t ≤ 1 := by
  rw [← I.mass_sum]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => (I.mass_pos i).le)

lemma normalized_energy {r : ℕ} (I : ComponentInstance r)
    (c : Fin r) (t : Fin I.k) (hs : 0 < I.partMass c t) :
    sqrt (∑ i, ∑ j,
      (if I.label c i = t then I.mass i / I.partMass c t else 0) *
      (if I.label c j = t then I.mass j / I.partMass c t else 0) *
      (-log (1 - I.density c i j))) = I.energy c t / I.partMass c t := by
  have heq : (∑ i, ∑ j,
      (if I.label c i = t then I.mass i / I.partMass c t else 0) *
      (if I.label c j = t then I.mass j / I.partMass c t else 0) *
      (-log (1 - I.density c i j))) = I.partEntropy c t / I.partMass c t ^ 2 := by
    simp only [ComponentInstance.partEntropy, Finset.sum_div, Finset.sum_filter]
    apply sum_congr rfl
    intro i hi
    by_cases hit : I.label c i = t
    · simp only [if_pos hit, Finset.sum_div]
      apply sum_congr rfl
      intro j hj
      by_cases hjt : I.label c j = t
      · simp only [if_pos hjt]
        ring
      · simp [hjt]
    · simp [hit]
  rw [heq, Real.sqrt_div (I.partEntropy_nonneg c t), Real.sqrt_sq hs.le]
  rfl

/-- Every positive-energy component eventually meets the random-minor threshold
and its bound fits below the desired bound in the ambient normalization. -/
theorem eventually_component_bounds {r : ℕ} (I : ComponentInstance r)
    (τ : ∀ n : ℕ, Fin n → Fin I.k)
    (hτ : ∀ i, Tendsto (fun n => classMass (τ n) i) atTop (𝓝 (I.mass i)))
    (c : Fin r) (t : Fin I.k) (hE : 0 < I.energy c t)
    {d B : ℝ} (hd : 0 < d) (hdE : d < I.energy c t)
    (hB : (1+d)*I.objective < B) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤ componentSize (τ n) (I.label c) t ∧
      d < sqrt (blockLambda ((τ n) ∘ componentMap (τ n) (I.label c) t) (I.density c)) ∧
      (1+d)*sqrt (blockLambda ((τ n) ∘ componentMap (τ n) (I.label c) t)
        (I.density c)) * (componentSize (τ n) (I.label c) t : ℝ) /
        sqrt (log (componentSize (τ n) (I.label c) t : ℝ)) ≤
        B*n/sqrt (log (n : ℝ)) := by
  let m := fun n => componentSize (τ n) (I.label c) t
  let L := fun n => sqrt (blockLambda ((τ n) ∘ componentMap (τ n) (I.label c) t)
    (I.density c))
  have hs := partMass_pos_of_energy_pos I c t hE
  have hdEs : d < I.energy c t / I.partMass c t := by
    apply (lt_div_iff₀ hs).mpr
    exact (mul_le_of_le_one_right hd.le (partMass_le_one I c t)).trans_lt hdE
  have hN : Tendsto (fun n : ℕ => (m n : ℝ)/n) atTop (𝓝 (I.partMass c t)) := by
    have h := tendsto_finsetSum (univ.filter (fun i => I.label c i = t))
      (fun i _ => hτ i)
    change Tendsto _ _ (𝓝 (I.partMass c t)) at h
    apply h.congr'
    exact Eventually.of_forall (fun n => (componentSize_ratio (τ n) (I.label c) t).symm)
  have hlocal (i : Fin I.k) :
      Tendsto (fun n => classMass ((τ n) ∘ componentMap (τ n) (I.label c) t) i)
        atTop (𝓝 (if I.label c i = t then I.mass i/I.partMass c t else 0)) := by
    by_cases hi : I.label c i = t
    · simp only [if_pos hi]
      apply ((hτ i).div hN hs.ne').congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [component_classMass_ratio hn, hi, if_true]
      rfl
    · simp only [if_neg hi]
      apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [component_classMass_ratio hn, hi, if_false]
  have hL : Tendsto L atTop (𝓝 (I.energy c t / I.partMass c t)) := by
    have h := (tendsto_finsetSum univ (fun i _ =>
      tendsto_finsetSum univ (fun j _ => ((hlocal i).mul (hlocal j)).mul_const
        (-log (1 - I.density c i j))))).sqrt
    rw [normalized_energy I c t hs] at h
    exact h
  have hH : Tendsto (fun n : ℕ => (1+d)*L n*((m n : ℝ)/n) *
      sqrt (log (n : ℝ)/log (m n : ℝ))) atTop (𝓝 ((1+d)*I.energy c t)) := by
    have h := ((hL.const_mul (1+d)).mul hN).mul (component_sqrt_log_ratio hs hN)
    convert h using 1
    field_simp [hs.ne']
  have hEB : (1+d)*I.energy c t < B :=
    (mul_le_mul_of_nonneg_left (I.energy_le_objective c t) (by linarith)).trans_lt hB
  have htop := componentOrder_atTop hs hN
  filter_upwards [htop.eventually_ge_atTop N, (tendsto_order.mp hL).1 d hdEs,
    (tendsto_order.mp hH).2 B hEB, htop.eventually_ge_atTop 2,
    (eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hn hLn hHn hm2 hn2
  refine ⟨hn, hLn, ?_⟩
  change (1+d)*L n*(m n : ℝ)/sqrt (log (m n : ℝ)) ≤ B*n/sqrt (log (n : ℝ))
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn2)
  have hmlog : 0 < log (m n : ℝ) := log_pos (by exact_mod_cast hm2)
  have hns := sqrt_pos.mpr hnlog
  have hms := sqrt_pos.mpr hmlog
  rw [sqrt_div hnlog.le] at hHn
  apply (div_le_div_iff₀ hms hns).mpr
  have hx : (1+d)*L n*((m n : ℝ)/n) *
      (sqrt (log (n : ℝ))/sqrt (log (m n : ℝ))) =
      ((1+d)*L n*(m n : ℝ)*sqrt (log (n : ℝ))) /
      ((n : ℝ)*sqrt (log (m n : ℝ))) := by ring
  rw [hx] at hHn
  have h := (div_lt_iff₀ (mul_pos hnp hms)).mp hHn
  nlinarith

end Construction
end HadwigerRamsey4Col
