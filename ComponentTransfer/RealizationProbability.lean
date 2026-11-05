import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Finset

namespace ComponentTransfer.Realization

/-- A finite family can be approximated simultaneously whenever its summed
mean square error is small. This avoids a separate union-bound estimate. -/
theorem exists_simultaneous_approximation {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (X : ι → Ω → ℝ) (a : ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω-a i)^2) μ)
    (hsmall : (∑ i ∈ s, ∫ ω, (X i ω-a i)^2 ∂μ) < ε^2) :
    ∃ ω, ∀ i ∈ s, |X i ω-a i| < ε := by
  have hex : ∃ ω, (∑ i ∈ s, (X i ω-a i)^2) < ε^2 := by
    by_contra! h
    have hsum := integrable_finsetSum s hInt
    have hh := integral_mono (integrable_const (ε^2)) hsum h
    rw [integral_const, probReal_univ, one_smul, integral_finsetSum s hInt] at hh
    linarith
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun i hi => ?_⟩
  have hle : (X i ω-a i)^2 ≤ ∑ j ∈ s, (X j ω-a j)^2 :=
    Finset.single_le_sum (f := fun j => (X j ω-a j)^2) (fun j _ => sq_nonneg _) hi
  have hs : |X i ω-a i|^2 < ε^2 := by simpa only [sq_abs] using hle.trans_lt hω
  nlinarith [abs_nonneg (X i ω-a i)]

/-- Choose a slowly increasing stage, with every fixed stage eventually attained. -/
theorem exists_slow_stage (N : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧ ∀ᶠ n : ℕ in atTop, N (m n) ≤ n := by
  classical
  let m := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  refine ⟨m, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (max k (N k))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn

/-- Finite simultaneous approximations give one deterministic choice at each
order, converging for every member of a countable list of tests. -/
theorem exists_diagonal_realization {Ω : ℕ → Type*} [∀ n, Nonempty (Ω n)]
    (X : ∀ n, ℕ → Ω n → ℝ) (a : ℕ → ℝ)
    (h : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, ∃ ω : Ω n,
      ∀ i ≤ m, |X n i ω-a i| < 1/((m : ℝ)+1)) :
    ∃ ω : ∀ n, Ω n, ∀ i, Tendsto (fun n => X n i (ω n)) atTop (𝓝 (a i)) := by
  classical
  choose N hN using fun m => eventually_atTop.mp (h m)
  obtain ⟨m, hm, hNm⟩ := exists_slow_stage N
  let ω : ∀ n, Ω n := fun n => if hn : N (m n) ≤ n then
    (hN (m n) n hn).choose else Classical.choice (inferInstance : Nonempty (Ω n))
  refine ⟨ω, fun i => ?_⟩
  have he : Tendsto (fun n : ℕ => 1/((m n : ℝ)+1)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => (m n : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hm)
    exact tendsto_const_nhds.div_atTop ht
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have heε := (tendsto_order.mp he).2 ε hε
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (hNm.and ((hm.eventually_ge_atTop i).and heε))
  refine ⟨N', fun n hn => ?_⟩
  obtain ⟨hnm, hmi, heps⟩ := hN' n hn
  have hw := (hN (m n) n hnm).choose_spec i hmi
  change dist (X n i (ω n)) (a i) < ε
  rw [Real.dist_eq]
  simpa only [ω, dif_pos hnm] using hw.trans heps

/-- Mean-square convergence for each test supplies a deterministic realization
of all tests simultaneously. -/
theorem exists_realization_of_mean_square {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, ℕ → Ω n → ℝ) (a : ℕ → ℝ)
    (hInt : ∀ n i, Integrable (fun ω => (X n i ω-a i)^2) (μ n))
    (hLim : ∀ i, Tendsto (fun n => ∫ ω, (X n i ω-a i)^2 ∂μ n) atTop (𝓝 0)) :
    ∃ ω : ∀ n, Ω n, ∀ i, Tendsto (fun n => X n i (ω n)) atTop (𝓝 (a i)) := by
  apply exists_diagonal_realization X a
  intro m
  have hsum : Tendsto (fun n => ∑ i ∈ Finset.range (m+1),
      ∫ ω, (X n i ω-a i)^2 ∂μ n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range (m+1)) (fun i _ => hLim i)
  have he : 0 < 1/((m : ℝ)+1) := by positivity
  filter_upwards [(tendsto_order.mp hsum).2 ((1/((m : ℝ)+1))^2) (sq_pos_of_pos he)] with n hn
  obtain ⟨ω, hω⟩ := exists_simultaneous_approximation (μ n) (Finset.range (m+1))
    (X n) a _ he (fun i _ => hInt n i) hn
  exact ⟨ω, fun i hi => hω i (Finset.mem_range.mpr (by omega))⟩

end ComponentTransfer.Realization
