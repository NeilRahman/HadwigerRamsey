import ComponentTransfer.RealizationConvergenceBridge
import ComponentTransfer.RealizationProbability

open MeasureTheory Filter Set
open scoped Topology

namespace ComponentTransfer.Realization

/-- The independent coupling supplies an arbitrary choice before an
approximation threshold has been reached. -/
noncomputable def ProbabilityCoupling.independent {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ProbabilityCoupling μ ν where
  law := μ.prod ν
  probability := inferInstance
  fst_mp := measurePreserving_fst
  snd_mp := measurePreserving_snd

/-- Convergence in the common coupling metric supplies one coupling at each
index, with every colour's cost tending to zero along the same sequence. -/
theorem CommonCutConverges.exists_coupling_sequence {r : ℕ} {V : ℕ → Type*}
    [∀ n, MeasurableSpace (V n)]
    (ν : ∀ n, Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (U : ∀ n, Fin r → Graphon (V n) (ν n)) (W : Fin r → Graphon α μ)
    (h : CommonCutConverges ν μ U W) :
    ∃ π : ∀ n, ProbabilityCoupling (ν n) μ,
      ∀ c, Tendsto (fun n => (π n).cost (U n c) (W c)) atTop (𝓝 0) := by
  classical
  have hstage (m : ℕ) : ∀ᶠ n in atTop, ∃ π : ProbabilityCoupling (ν n) μ,
      ∀ c, π.cost (U n c) (W c) < 1 / ((m : ℝ) + 1) :=
    h _ (by positivity)
  choose N hN using fun m => eventually_atTop.mp (hstage m)
  obtain ⟨stage, hstageTop, hready⟩ := exists_slow_stage N
  let π : ∀ n, ProbabilityCoupling (ν n) μ := fun n =>
    if hn : N (stage n) ≤ n then (hN (stage n) n hn).choose
    else ProbabilityCoupling.independent (ν n) μ
  refine ⟨π, fun c => ?_⟩
  have hbound : ∀ᶠ n in atTop,
      (π n).cost (U n c) (W c) ≤ 1 / ((stage n : ℝ) + 1) := by
    filter_upwards [hready] with n hn
    dsimp only [π]
    rw [dif_pos hn]
    exact ((hN (stage n) n hn).choose_spec c).le
  have hzero : Tendsto (fun n => 1 / ((stage n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp hstageTop)
  exact squeeze_zero' (Eventually.of_forall fun n => (π n).cost_nonneg _ _) hbound hzero

/-- Finite common cut convergence, when every carrier is nonempty, can be
realized by an explicit sequence of common probability couplings. -/
theorem FiniteCommonCutConverges.exists_coupling_sequence {r : ℕ} {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : ∀ n, Fin r → V n → V n → ℝ)
    (hAsymm : ∀ n c i j, A n c i j = A n c j i)
    (hA : ∀ n c i j, A n c i j ∈ Icc (0 : ℝ) 1)
    (W : Fin r → Graphon α μ) (h : FiniteCommonCutConverges μ A hAsymm hA W) :
    ∃ π : ∀ n, ProbabilityCoupling (uniformFiniteMeasure (V n)) μ,
      ∀ c, Tendsto (fun n => (π n).cost
        (markedGraphon (A n c) (hAsymm n c) (hA n c) id measurable_id) (W c))
        atTop (𝓝 0) := by
  apply CommonCutConverges.exists_coupling_sequence (fun n => uniformFiniteMeasure (V n)) μ
    (fun n c => markedGraphon (A n c) (hAsymm n c) (hA n c) id measurable_id) W
  intro ε hε
  filter_upwards [h ε hε] with n hn
  obtain ⟨_, π, hπ⟩ := hn
  exact ⟨π, hπ⟩

end ComponentTransfer.Realization
