import Mathlib

open scoped BigOperators Topology ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory Finset

namespace HadwigerRamsey4Col.Realization

lemma integral_sq_error_eq_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ) (a : ℝ) :
    (∫ ω, (X ω-a)^2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ)-a)^2 := by
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have he : (fun ω => (X ω-a)^2) = (fun ω => X ω^2-(2*a)*X ω+a^2) := by
    funext ω
    ring
  rw [he]
  have hadd := integral_add (hX.integrable_sq.sub (hXi.const_mul (2*a))) (integrable_const (a^2))
  simp only [Pi.sub_apply] at hadd
  rw [hadd]
  have hsub := integral_sub hX.integrable_sq (hXi.const_mul (2*a))
  rw [hsub, integral_const_mul, integral_const, probReal_univ, one_smul, variance_eq_sub hX]
  change (∫ ω, X ω^2 ∂μ) - (2*a)*(∫ ω, X ω ∂μ) + a^2 =
    (∫ ω, X ω^2 ∂μ) - (∫ ω, X ω ∂μ)^2 + ((∫ ω, X ω ∂μ)-a)^2
  ring

lemma mean_square_tendsto_of_mean_variance {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (X : ∀ n, Ω n → ℝ)
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (a : ℝ)
    (hm : Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 a))
    (hv : Tendsto (fun n => variance (X n) (μ n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n ω-a)^2 ∂μ n) atTop (𝓝 0) := by
  simp_rw [integral_sq_error_eq_variance _ _ (hX _) a]
  simpa using hv.add ((hm.sub_const a).pow 2)

lemma memLp_of_unit_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hm : Measurable X) (hb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) : MemLp X 2 μ :=
  memLp_of_bounded (Eventually.of_forall hb) hm.aestronglyMeasurable 2

lemma covariance_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) (hYb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) :
    covariance X Y μ ≤ 1 := by
  rw [covariance_eq_sub hX hY]
  have hx : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg (fun ω => (hXb ω).1)
  have hy : 0 ≤ ∫ ω, Y ω ∂μ := integral_nonneg (fun ω => (hYb ω).1)
  have hxy : (∫ ω, X ω * Y ω ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫ _ω : Ω, (1 : ℝ) ∂μ := integral_mono (hX.integrable_mul hY)
        (integrable_const _) (fun ω => mul_le_one₀ (hXb ω).2 (hYb ω).1 (hYb ω).2)
      _ = 1 := by simp
  change (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) ≤ 1
  nlinarith

/-- Averages of bounded local statistics have variance controlled by the
fraction of pairs which are not known to be independent. -/
theorem variance_average_le {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : J → Ω → ℝ)
    (hm : ∀ j, Measurable (X j)) (hb : ∀ j ω, 0 ≤ X j ω ∧ X j ω ≤ 1)
    (bad : Finset (J × J))
    (hi : ∀ i j, (i,j) ∉ bad → IndepFun (X i) (X j) μ) :
    variance (fun ω => (∑ j, X j ω)/(Fintype.card J : ℝ)) μ ≤
      (bad.card : ℝ)/(Fintype.card J : ℝ)^2 := by
  classical
  have hLp := fun j => memLp_of_unit_interval μ (hm j) (hb j)
  have hcov : ∀ i j, covariance (X i) (X j) μ ≤ if (i,j) ∈ bad then 1 else 0 := by
    intro i j
    split_ifs with h
    · exact covariance_le_one μ (hLp i) (hLp j) (hb i) (hb j)
    · rw [(hi i j h).covariance_eq_zero (hLp i) (hLp j)]
  have hsum : (∑ i, ∑ j, covariance (X i) (X j) μ) ≤ (bad.card : ℝ) := by
    calc
      _ ≤ ∑ i, ∑ j, if (i,j) ∈ bad then (1 : ℝ) else 0 :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => hcov i j))
      _ = bad.card := by
        rw [← Fintype.sum_prod_type (f := fun p : J × J => if p ∈ bad then (1 : ℝ) else 0)]
        simp
  have he : (fun ω => (∑ j, X j ω)/(Fintype.card J : ℝ)) =
      (fun ω => (Fintype.card J : ℝ)⁻¹ * (∑ j, X j ω)) := by
    funext ω
    rw [div_eq_mul_inv, mul_comm]
  rw [he, variance_const_mul, variance_fun_sum hLp]
  calc
    _ ≤ ((Fintype.card J : ℝ)⁻¹)^2 * bad.card :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring

/-- If individual expectations agree except at a small set of indices, the
error of the normalized expectation is at most that set's relative size. -/
theorem mean_average_error_le {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : J → Ω → ℝ) (a : J → ℝ)
    (hm : ∀ j, Measurable (X j)) (hb : ∀ j ω, 0 ≤ X j ω ∧ X j ω ≤ 1)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (bad : Finset J)
    (he : ∀ j, j ∉ bad → (∫ ω, X j ω ∂μ) = a j) :
    |(∫ ω, (∑ j, X j ω)/(Fintype.card J : ℝ) ∂μ) -
      (∑ j, a j)/(Fintype.card J : ℝ)| ≤ (bad.card : ℝ)/(Fintype.card J : ℝ) := by
  classical
  have hLp := fun j => memLp_of_unit_interval μ (hm j) (hb j)
  have hInt := fun j => (hLp j).integrable (by norm_num)
  have hterm : ∀ j, |(∫ ω, X j ω ∂μ)-a j| ≤ if j ∈ bad then (1 : ℝ) else 0 := by
    intro j
    split_ifs with h
    · have h0 : 0 ≤ ∫ ω, X j ω ∂μ := integral_nonneg (fun ω => (hb j ω).1)
      have h1 : (∫ ω, X j ω ∂μ) ≤ 1 := by
        calc
          _ ≤ ∫ _ω : Ω, (1 : ℝ) ∂μ := integral_mono (hInt j) (integrable_const _)
            (fun ω => (hb j ω).2)
          _ = 1 := by simp
      exact abs_le.mpr ⟨by linarith [(ha j).2], by linarith [(ha j).1]⟩
    · rw [he j h, sub_self, abs_zero]
  have hsum : |(∑ j, ∫ ω, X j ω ∂μ)-(∑ j, a j)| ≤ (bad.card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |(∫ ω, X j ω ∂μ)-a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, if j ∈ bad then (1 : ℝ) else 0 := sum_le_sum (fun j _ => hterm j)
      _ = bad.card := by simp
  rw [integral_div, integral_finsetSum _ (fun j _ => hInt j), ← sub_div,
    abs_div, abs_of_nonneg (a := (Fintype.card J : ℝ)) (Nat.cast_nonneg (Fintype.card J))]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end HadwigerRamsey4Col.Realization
