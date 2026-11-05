import HadwigerRamsey4Col.Realization
import HadwigerRamsey4Col.RealizationConvergencePullback
import HadwigerRamsey4Col.RealizationConvergenceSelection
import HadwigerRamsey4Col.RealizationCommonMaps

open scoped BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter Finset Set

namespace HadwigerRamsey4Col.Realization

variable {α : Type*} [MeasurableSpace α]

/-- The target-coordinate law conditioned on one finite source vertex of a
probability coupling. -/
noncomputable def couplingConditionalMeasure {n : ℕ}
    (ρ : Measure (Fin n × α)) (v : Fin n) : Measure α :=
  (cellConditionalMeasure ρ Prod.fst v).map Prod.snd

theorem couplingConditionalMeasure_probability {n : ℕ}
    (ρ : Measure (Fin n × α)) [IsProbabilityMeasure ρ] (hn : 0 < n)
    (hmass : ∀ v, ρ.real (Prod.fst ⁻¹' {v}) = 1/(n : ℝ)) (v : Fin n) :
    IsProbabilityMeasure (couplingConditionalMeasure ρ v) := by
  letI := cellConditionalMeasure_probability ρ hn Prod.fst hmass v
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

theorem fractionalPatternAverage_couplingConditionalMeasure {r k n : ℕ}
    (ρ : Measure (Fin n × α)) [IsProbabilityMeasure ρ]
    (P : Pattern r k) (hn : 0 < n) (G : Fin r → SimpleGraph (Fin n))
    (U : Fin r → Graphon (Fin n × α) ρ)
    (hmass : ∀ v, ρ.real (Prod.fst ⁻¹' {v}) = 1/(n : ℝ))
    (hU : ∀ c, ∀ᵐ p ∂ρ.prod ρ,
      (U c).toAEEqFun p = Graphon.adjIndicator (G c) p.1.1 p.2.1)
    (mark : α → Fin k) (hmark : Measurable mark) :
    fractionalPatternAverage (fun v => (couplingConditionalMeasure ρ v).map mark)
      (finitePatternWeight P G) P.label =
      markedDensity P U (fun i => Prod.snd ⁻¹' (mark ⁻¹' {i})) := by
  simp only [couplingConditionalMeasure, Measure.map_map hmark measurable_snd]
  exact fractionalPatternAverage_eq_markedDensity ρ P hn G U Prod.fst measurable_fst
    hmass hU (mark ∘ Prod.snd) (hmark.comp measurable_snd)

/-- Honest common probability couplings from a finite graph sequence to the
target graphon produce one target point per vertex realizing every prescribed
countable family of finite marked tests. -/
theorem exists_realization_all_marked_patterns_of_couplings
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (ρ : ∀ n, Measure (Fin (N n) × α)) [∀ n, IsProbabilityMeasure (ρ n)]
    (hmass : ∀ n v, (ρ n).real (Prod.fst ⁻¹' {v}) = 1/(N n : ℝ))
    (hsnd : ∀ n, MeasurePreserving Prod.snd (ρ n) μ)
    (U : ∀ n, Fin r → Graphon (Fin (N n) × α) (ρ n))
    (W : Fin r → Graphon α μ)
    (hU : ∀ n c, ∀ᵐ p ∂(ρ n).prod (ρ n),
      (U n c).toAEEqFun p = Graphon.adjIndicator (G n c) p.1.1 p.2.1)
    (hcut : ∀ c, Tendsto (fun n => Graphon.cutNormDiff (U n c)
      (Graphon.pullback (W c) Prod.snd (hsnd n))) atTop (𝓝 0))
    (k : ℕ → ℕ) (mark : ∀ j, α → Fin (k j)) (hmark : ∀ j, Measurable (mark j)) :
    ∃ x : ∀ n, Fin (N n) → α, ∀ j (P : Pattern r (k j)),
      Tendsto (fun n => finitePatternDensity P (G n) (mark j ∘ x n)) atTop
        (𝓝 (markedDensity P W (fun i => (mark j) ⁻¹' {i}))) := by
  have hNpos (n : ℕ) : 0 < N n := by
    obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure (ρ n)
    exact lt_of_le_of_lt (Nat.zero_le _) z.1.isLt
  let T := Σ j : ℕ, Pattern r (k j)
  have : Countable T := by dsimp [T]; infer_instance
  have : Nonempty T := by
    refine ⟨⟨0, ⟨0, ⊥, ?_, ?_⟩⟩⟩
    · exact fun e => isEmptyElim e
    · exact Fin.elim0
  let ν := fun n v => couplingConditionalMeasure (ρ n) v
  have hν (n : ℕ) (v : Fin (N n)) : IsProbabilityMeasure (ν n v) :=
    couplingConditionalMeasure_probability (ρ n) (hNpos n) (hmass n) v
  have htargets (t : T) :
      Tendsto (fun n => fractionalPatternAverage
        (fun v => (ν n v).map (mark t.1)) (finitePatternWeight t.2 (G n)) t.2.label) atTop
        (𝓝 (markedDensity t.2 W (fun i => (mark t.1) ⁻¹' {i}))) := by
    have hh := markedDensity_tendsto_varying ρ t.2 U W (fun _ => Prod.snd) hsnd
      (fun i => (mark t.1) ⁻¹' {i})
      (fun i => (hmark t.1) (measurableSet_singleton i)) hcut
    apply hh.congr'
    exact Eventually.of_forall (fun n =>
      (fractionalPatternAverage_couplingConditionalMeasure (ρ n) t.2 (hNpos n) (G n)
        (U n) (hmass n) (hU n) (mark t.1) (hmark t.1)).symm)
  obtain ⟨x, _, hpatterns⟩ := exists_countable_marked_pattern_realization (ι := T)
    N hN ν (fun t => t.2.1) (fun t => k t.1) (fun t => mark t.1) (fun t => hmark t.1)
    (fun n t => finitePatternWeight t.2 (G n))
    (fun n t => finitePatternWeight_bounds t.2 (G n))
    (fun t => t.2.label) (fun t => markedDensity t.2 W (fun i => (mark t.1) ⁻¹' {i}))
    (fun _ _ => True) (fun _ => Eventually.of_forall fun _ => trivial) htargets
  exact ⟨x, fun j P => hpatterns ⟨j,P⟩⟩

/-- Extend point choices over an arbitrary finite initial segment. -/
noncomputable def extendVertexSamples (a₀ : α) (N : ℕ → ℕ) (d : ℕ)
    (x : ∀ n, Fin (N (n + d)) → α) (n : ℕ) (v : Fin (N n)) : α :=
  if h : d ≤ n then
    x (n-d) (Fin.cast (congrArg N (Nat.sub_add_cancel h)).symm v)
  else a₀

@[simp] theorem extendVertexSamples_add (a₀ : α) (N : ℕ → ℕ) (d : ℕ)
    (x : ∀ n, Fin (N (n + d)) → α) (n : ℕ) :
    extendVertexSamples a₀ N d x (n+d) = x n := by
  funext v
  simp only [extendVertexSamples, dif_pos (Nat.le_add_left d n)]
  have h : n + d - d = n := Nat.add_sub_cancel_right n d
  have heq (m : ℕ) (hm : m = n) :
      x m (Fin.cast (congrArg (fun t => N (t+d)) hm.symm) v) = x n v := by
    subst m
    rfl
  exact heq _ h

/-- Finite initial terms have no effect on simultaneous marked-test limits. -/
theorem exists_realization_of_tail [Nonempty α] {r : ℕ}
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (k : ℕ → ℕ) (mark : ∀ j, α → Fin (k j))
    (b : ∀ j, Pattern r (k j) → ℝ) (d : ℕ)
    (htail : ∃ x : ∀ n, Fin (N (n+d)) → α, ∀ j (P : Pattern r (k j)),
      Tendsto (fun n => finitePatternDensity P (G (n+d)) (mark j ∘ x n))
        atTop (𝓝 (b j P))) :
    ∃ x : ∀ n, Fin (N n) → α, ∀ j (P : Pattern r (k j)),
      Tendsto (fun n => finitePatternDensity P (G n) (mark j ∘ x n))
        atTop (𝓝 (b j P)) := by
  obtain ⟨x, hx⟩ := htail
  refine ⟨extendVertexSamples (Classical.choice ‹Nonempty α›) N d x, fun j P => ?_⟩
  apply (tendsto_add_atTop_iff_nat d).mp
  simpa using hx j P

lemma adjIndicator_symm_all {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    Graphon.adjIndicator G i j = Graphon.adjIndicator G j i := by
  simp only [Graphon.adjIndicator, G.adj_comm]

lemma adjIndicator_bounds_all {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    Graphon.adjIndicator G i j ∈ Icc (0 : ℝ) 1 := by
  unfold Graphon.adjIndicator
  split_ifs <;> norm_num

/-- Common coloured cut convergence for finite graphs, allowing empty carriers
at arbitrary initial indices. -/
def FiniteGraphCommonCutConverges (μ : Measure α) [IsProbabilityMeasure μ]
    {r : ℕ} (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (W : Fin r → Graphon α μ) : Prop :=
  FiniteCommonCutConverges μ (fun n c => Graphon.adjIndicator (G n c))
    (fun n c => adjIndicator_symm_all (G n c))
    (fun n c => adjIndicator_bounds_all (G n c)) W

theorem exists_realization_of_finite_common_cut_pos
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (hconv : FiniteGraphCommonCutConverges μ N G W)
    (k : ℕ → ℕ) (mark : ∀ j, α → Fin (k j)) (hmark : ∀ j, Measurable (mark j)) :
    ∃ x : ∀ n, Fin (N n) → α, ∀ j (P : Pattern r (k j)),
      Tendsto (fun n => finitePatternDensity P (G n) (mark j ∘ x n)) atTop
        (𝓝 (markedDensity P W (fun i => (mark j) ⁻¹' {i}))) := by
  have : ∀ n, Nonempty (Fin (N n)) := fun n => ⟨⟨0, hNpos n⟩⟩
  obtain ⟨π, hπ⟩ := FiniteCommonCutConverges.exists_coupling_sequence μ
    (fun n c => Graphon.adjIndicator (G n c))
    (fun n c => adjIndicator_symm_all (G n c))
    (fun n c => adjIndicator_bounds_all (G n c)) W hconv
  let V := fun n c => markedGraphon (μ := uniformFiniteMeasure (Fin (N n)))
    (Graphon.adjIndicator (G n c)) (adjIndicator_symm_all (G n c))
    (adjIndicator_bounds_all (G n c)) id measurable_id
  let U := fun n c => Graphon.pullback (V n c) Prod.fst (π n).fst_mp
  have hmass (n : ℕ) (v : Fin (N n)) :
      (π n).law.real (Prod.fst ⁻¹' {v}) = 1/(N n : ℝ) := by
    have h := congrArg ENNReal.toReal ((π n).fst_mp.measure_preimage
      (measurableSet_singleton v).nullMeasurableSet)
    change (π n).law.real (Prod.fst ⁻¹' {v}) =
      (uniformFiniteMeasure (Fin (N n))).real {v} at h
    rw [h]
    simpa using uniformFiniteMeasure_singleton v
  have hU (n : ℕ) (c : Fin r) : ∀ᵐ p ∂(π n).law.prod (π n).law,
      (U n c).toAEEqFun p = Graphon.adjIndicator (G n c) p.1.1 p.2.1 := by
    filter_upwards [Graphon.pullback_ae (V n c) Prod.fst (π n).fst_mp] with p hp
    rw [hp]
    exact markedGraphon_uniform_apply uniformFiniteMeasure_singleton
      (Graphon.adjIndicator (G n c)) (adjIndicator_symm_all (G n c))
      (adjIndicator_bounds_all (G n c)) id measurable_id p.1.1 p.2.1
  exact exists_realization_all_marked_patterns_of_couplings μ N hN G (fun n => (π n).law)
    hmass (fun n => (π n).snd_mp) U W hU hπ k mark hmark

/-- The all-pattern realization theorem under the usual common coupling
convergence hypothesis, with only growth of the vertex orders required. -/
theorem exists_realization_of_finite_common_cut
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n))) (W : Fin r → Graphon α μ)
    (hconv : FiniteGraphCommonCutConverges μ N G W)
    (k : ℕ → ℕ) (mark : ∀ j, α → Fin (k j)) (hmark : ∀ j, Measurable (mark j)) :
    ∃ x : ∀ n, Fin (N n) → α, ∀ j (P : Pattern r (k j)),
      Tendsto (fun n => finitePatternDensity P (G n) (mark j ∘ x n)) atTop
        (𝓝 (markedDensity P W (fun i => (mark j) ⁻¹' {i}))) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  obtain ⟨d, hd⟩ := eventually_atTop.mp (hN.eventually_gt_atTop 0)
  have hpos (n : ℕ) : 0 < N (n+d) := hd (n+d) (Nat.le_add_left d n)
  have hconv' : FiniteGraphCommonCutConverges μ (fun n => N (n+d))
      (fun n => G (n+d)) W := by
    intro ε hε
    exact (tendsto_add_atTop_nat d).eventually (hconv ε hε)
  have hN' : Tendsto (fun n => N (n+d)) atTop atTop :=
    hN.comp (tendsto_add_atTop_nat d)
  exact exists_realization_of_tail N G k mark
    (fun j P => markedDensity P W (fun i => (mark j) ⁻¹' {i})) d
    (exists_realization_of_finite_common_cut_pos μ (fun n => N (n+d)) hpos hN'
      (fun n => G (n+d)) W hconv' k mark hmark)

end HadwigerRamsey4Col.Realization
