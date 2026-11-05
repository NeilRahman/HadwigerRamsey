import ComponentTransfer.RealizationProbabilityStatistics

open scoped BigOperators Topology ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory Finset Set

namespace ComponentTransfer.Realization

/-- Simultaneous approximation can also preserve any probability-one condition. -/
theorem exists_simultaneous_approximation_with {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (X : ι → Ω → ℝ) (a : ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω)
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω-a i)^2) μ)
    (hsmall : (∑ i ∈ s, ∫ ω, (X i ω-a i)^2 ∂μ) < ε^2) :
    ∃ ω, P ω ∧ ∀ i ∈ s, |X i ω-a i| < ε := by
  have hex : ∃ ω, P ω ∧ (∑ i ∈ s, (X i ω-a i)^2) < ε^2 := by
    by_contra! h
    have hsum := integrable_finsetSum s hInt
    have hh := integral_mono_ae (integrable_const (ε^2)) hsum
      (hP.mono (fun ω hω => h ω hω))
    rw [integral_const, probReal_univ, one_smul, integral_finsetSum s hInt] at hh
    linarith
  obtain ⟨ω, hp, hω⟩ := hex
  refine ⟨ω, hp, fun i hi => ?_⟩
  have hle : (X i ω-a i)^2 ≤ ∑ j ∈ s, (X j ω-a j)^2 :=
    Finset.single_le_sum (f := fun j => (X j ω-a j)^2) (fun j _ => sq_nonneg _) hi
  have hs : |X i ω-a i|^2 < ε^2 := by simpa only [sq_abs] using hle.trans_lt hω
  nlinarith [abs_nonneg (X i ω-a i)]

/-- Deterministic realization of a countable family preserving a probability-one event. -/
theorem exists_realization_of_mean_square_with {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, ℕ → Ω n → ℝ) (a : ℕ → ℝ)
    (P : ∀ n, Ω n → Prop) (hP : ∀ n, ∀ᵐ ω ∂μ n, P n ω)
    (hInt : ∀ n i, Integrable (fun ω => (X n i ω-a i)^2) (μ n))
    (hLim : ∀ i, Tendsto (fun n => ∫ ω, (X n i ω-a i)^2 ∂μ n) atTop (𝓝 0)) :
    ∃ ω : ∀ n, Ω n, (∀ n, P n (ω n)) ∧
      ∀ i, Tendsto (fun n => X n i (ω n)) atTop (𝓝 (a i)) := by
  let Ω' := fun n => {ω : Ω n // P n ω}
  have : ∀ n, Nonempty (Ω' n) := fun n => by
    obtain ⟨ω, hω⟩ := (hP n).exists
    exact ⟨⟨ω,hω⟩⟩
  have hdiag : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, ∃ ω : Ω' n,
      ∀ i ≤ m, |X n i ω.val-a i| < 1/((m : ℝ)+1) := by
    intro m
    have hsum : Tendsto (fun n => ∑ i ∈ Finset.range (m+1),
        ∫ ω, (X n i ω-a i)^2 ∂μ n) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.range (m+1)) (fun i _ => hLim i)
    have he : 0 < 1/((m : ℝ)+1) := by positivity
    filter_upwards [(tendsto_order.mp hsum).2 ((1/((m : ℝ)+1))^2) (sq_pos_of_pos he)] with n hn
    obtain ⟨ω, hp, hω⟩ := exists_simultaneous_approximation_with (μ n) (Finset.range (m+1))
      (X n) a _ he (P n) (hP n) (fun i _ => hInt n i) hn
    exact ⟨⟨ω,hp⟩, fun i hi => hω i (Finset.mem_range.mpr (by omega))⟩
  obtain ⟨ω, hω⟩ := exists_diagonal_realization (Ω := Ω') (fun n i x => X n i x.val) a hdiag
  exact ⟨fun n => (ω n).val, fun n => (ω n).property, hω⟩

lemma marking_measurePreserving {α L : Type*} [MeasurableSpace α] [MeasurableSpace L]
    {n : ℕ} (μ : Fin n → Measure α) [∀ v, IsProbabilityMeasure (μ v)]
    (π : α → L) (hπ : Measurable π) :
    MeasurePreserving (fun ω : Fin n → α => π ∘ ω) (Measure.pi μ)
      (Measure.pi (fun v => (μ v).map π)) := by
  have : ∀ v, IsProbabilityMeasure ((μ v).map π) := fun v =>
    Measure.isProbabilityMeasure_map hπ.aemeasurable
  exact measurePreserving_pi μ (fun v => (μ v).map π) (fun v => ⟨hπ,rfl⟩)

/-- A single sequence of sampled points realizes countably many finite tests,
each with its own finite measurable marking of the point space. -/
theorem exists_marked_pattern_realization {α : Type*} [MeasurableSpace α]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ∀ n, Fin (N n) → Measure α) [∀ n v, IsProbabilityMeasure (μ n v)]
    (m k : ℕ → ℕ) (π : ∀ i, α → Fin (k i)) (hπ : ∀ i, Measurable (π i))
    (w : ∀ n i, (Fin (m i) → Fin (N n)) → ℝ)
    (hw : ∀ n i f, 0 ≤ w n i f ∧ w n i f ≤ 1)
    (a : ∀ i, Fin (m i) → Fin (k i)) (b : ℕ → ℝ)
    (P : ∀ n, (Fin (N n) → α) → Prop) (hP : ∀ n, ∀ᵐ ω ∂Measure.pi (μ n), P n ω)
    (hb : ∀ i, Tendsto (fun n => fractionalPatternAverage
      (fun v => (μ n v).map (π i)) (w n i) (a i)) atTop (𝓝 (b i))) :
    ∃ ω : ∀ n, Fin (N n) → α, (∀ n, P n (ω n)) ∧ ∀ i,
      Tendsto (fun n => weightedPatternAverage (w n i) (a i) (π i ∘ ω n)) atTop (𝓝 (b i)) := by
  have hprob (n i : ℕ) (v : Fin (N n)) :
      IsProbabilityMeasure ((μ n v).map (π i)) :=
    Measure.isProbabilityMeasure_map (hπ i).aemeasurable
  have hmap n i := marking_measurePreserving (μ n) (π i) (hπ i)
  have hLp n i := weightedPatternAverage_memLp (fun v => (μ n v).map (π i))
    (w n i) (hw n i) (a i)
  apply exists_realization_of_mean_square_with (fun n => Measure.pi (μ n))
    (fun n i ω => weightedPatternAverage (w n i) (a i) (π i ∘ ω)) b P hP
  · intro n i
    exact ((hLp n i).comp_measurePreserving (hmap n i) |>.sub (memLp_const (b i))).integrable_sq
  · intro i
    have ht := weightedPatternAverage_mean_square_tendsto N hN
      (fun n v => (μ n v).map (π i)) (fun n => w n i) (fun n => hw n i) (a i) (hb i)
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    have hF := ((hLp n i).sub (memLp_const (b i))).integrable_sq.aestronglyMeasurable
    have hh := integral_map (hmap n i).aemeasurable ((hmap n i).map_eq.symm ▸ hF)
    rw [(hmap n i).map_eq] at hh
    exact hh

/-- The marked realization theorem indexed by any nonempty countable test type. -/
theorem exists_countable_marked_pattern_realization {α ι : Type*}
    [MeasurableSpace α] [Nonempty ι] [Countable ι]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ∀ n, Fin (N n) → Measure α) [∀ n v, IsProbabilityMeasure (μ n v)]
    (m k : ι → ℕ) (π : ∀ i, α → Fin (k i)) (hπ : ∀ i, Measurable (π i))
    (w : ∀ n i, (Fin (m i) → Fin (N n)) → ℝ)
    (hw : ∀ n i f, 0 ≤ w n i f ∧ w n i f ≤ 1)
    (a : ∀ i, Fin (m i) → Fin (k i)) (b : ι → ℝ)
    (P : ∀ n, (Fin (N n) → α) → Prop) (hP : ∀ n, ∀ᵐ ω ∂Measure.pi (μ n), P n ω)
    (hb : ∀ i, Tendsto (fun n => fractionalPatternAverage
      (fun v => (μ n v).map (π i)) (w n i) (a i)) atTop (𝓝 (b i))) :
    ∃ ω : ∀ n, Fin (N n) → α, (∀ n, P n (ω n)) ∧ ∀ i,
      Tendsto (fun n => weightedPatternAverage (w n i) (a i) (π i ∘ ω n)) atTop (𝓝 (b i)) := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  obtain ⟨ω, hp, hω⟩ := exists_marked_pattern_realization N hN μ
    (fun j => m (e j)) (fun j => k (e j)) (fun j => π (e j)) (fun j => hπ (e j))
    (fun n j => w n (e j)) (fun n j => hw n (e j)) (fun j => a (e j))
    (fun j => b (e j)) P hP (fun j => hb (e j))
  refine ⟨ω, hp, fun i => ?_⟩
  obtain ⟨j,rfl⟩ := he i
  exact hω j

end ComponentTransfer.Realization
