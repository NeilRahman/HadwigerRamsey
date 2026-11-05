import HadwigerRamsey4Col.RealizationProbability
import HadwigerRamsey4Col.RealizationProbabilityMoments
import HadwigerRamsey4Col.RealizationProbabilityLabels
import HadwigerRamsey4Col.RealizationCombinatorics

open scoped BigOperators Topology ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory Finset Set

namespace HadwigerRamsey4Col.Realization

noncomputable def weightedPatternAverage {m n : ℕ} {K : Type*}
    (w : (Fin m → Fin n) → ℝ) (a : Fin m → K) (ω : Fin n → K) : ℝ :=
  (∑ f, w f * labelPattern f a ω)/(n : ℝ)^m

noncomputable def fractionalPatternAverage {m n : ℕ} {K : Type*} [MeasurableSpace K]
    (μ : Fin n → Measure K) (w : (Fin m → Fin n) → ℝ) (a : Fin m → K) : ℝ :=
  (∑ f, w f * ∏ i, (μ (f i)).real {a i})/(n : ℝ)^m

lemma weightedPattern_measurable {m n : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (w : (Fin m → Fin n) → ℝ) (a : Fin m → K) (f : Fin m → Fin n) :
    Measurable (fun ω => w f * labelPattern f a ω) :=
  (labelPattern_measurable f a).const_mul _

lemma weightedPattern_bounds {m n : ℕ} {K : Type*}
    (w : (Fin m → Fin n) → ℝ) (hw : ∀ f, 0 ≤ w f ∧ w f ≤ 1)
    (a : Fin m → K) (f : Fin m → Fin n) (ω : Fin n → K) :
    0 ≤ w f * labelPattern f a ω ∧ w f * labelPattern f a ω ≤ 1 :=
  ⟨mul_nonneg (hw f).1 (labelPattern_bounds f a ω).1,
    mul_le_one₀ (hw f).2 (labelPattern_bounds f a ω).1 (labelPattern_bounds f a ω).2⟩

lemma weightedPatternAverage_memLp {m n : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Fin n → Measure K) [∀ v, IsProbabilityMeasure (μ v)]
    (w : (Fin m → Fin n) → ℝ) (hw : ∀ f, 0 ≤ w f ∧ w f ≤ 1) (a : Fin m → K) :
    MemLp (weightedPatternAverage w a) 2 (Measure.pi μ) := by
  have h : MemLp (fun ω => ∑ f, w f * labelPattern f a ω) 2 (Measure.pi μ) :=
    memLp_finsetSum Finset.univ (fun f _ =>
    memLp_of_unit_interval (Measure.pi μ) (weightedPattern_measurable w a f)
      (weightedPattern_bounds w hw a f))
  change MemLp (fun ω => (∑ f, w f * labelPattern f a ω)/(n : ℝ)^m) 2 (Measure.pi μ)
  simpa only [div_eq_mul_inv] using h.mul_const (((n : ℝ)^m)⁻¹)

/-- Only vertex maps with repeated vertices contribute to expectation error. -/
theorem weightedPatternAverage_mean_error {m n : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Fin n → Measure K) [∀ v, IsProbabilityMeasure (μ v)]
    (w : (Fin m → Fin n) → ℝ) (hw : ∀ f, 0 ≤ w f ∧ w f ≤ 1)
    (a : Fin m → K) (hn : 0 < n) :
    |(∫ ω, weightedPatternAverage w a ω ∂Measure.pi μ)-fractionalPatternAverage μ w a| ≤
      (m : ℝ)^2/n := by
  classical
  let bad := (univ : Finset (Fin m → Fin n)).filter (fun f => ¬Function.Injective f)
  have hp : ∀ f : Fin m → Fin n, 0 ≤ (∏ i, (μ (f i)).real {a i}) ∧
      (∏ i, (μ (f i)).real {a i}) ≤ 1 := by
    intro f
    exact ⟨prod_nonneg (fun _ _ => measureReal_nonneg),
      prod_le_one (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_le_one)⟩
  have hh := mean_average_error_le (Measure.pi μ)
    (fun f ω => w f * labelPattern f a ω) (fun f => w f * ∏ i, (μ (f i)).real {a i})
    (weightedPattern_measurable w a) (weightedPattern_bounds w hw a)
    (fun f => ⟨mul_nonneg (hw f).1 (hp f).1,
      mul_le_one₀ (hw f).2 (hp f).1 (hp f).2⟩) bad (by
        intro f hf
        have hfi : Function.Injective f := by simpa [bad] using hf
        rw [integral_const_mul, integral_labelPattern_of_injective μ f hfi a])
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hh
  exact hh.trans (noninjective_fraction_le m n hn)

/-- Only pairs of vertex maps with overlapping images contribute covariance. -/
theorem weightedPatternAverage_variance {m n : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Fin n → Measure K) [∀ v, IsProbabilityMeasure (μ v)]
    (w : (Fin m → Fin n) → ℝ) (hw : ∀ f, 0 ≤ w f ∧ w f ≤ 1)
    (a : Fin m → K) (hn : 0 < n) :
    variance (weightedPatternAverage w a) (Measure.pi μ) ≤ (m : ℝ)^2/n := by
  classical
  let bad := (univ : Finset ((Fin m → Fin n) × (Fin m → Fin n))).filter
    (fun fg => ∃ i j, fg.1 i = fg.2 j)
  have hh := variance_average_le (Measure.pi μ) (fun f ω => w f * labelPattern f a ω)
    (weightedPattern_measurable w a) (weightedPattern_bounds w hw a) bad (by
      intro f g hfg
      have hd : Disjoint (Set.range f) (Set.range g) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨i, rfl⟩ ⟨j, hj⟩
        apply hfg
        exact mem_filter.mpr ⟨mem_univ _, ⟨i,j,hj.symm⟩⟩
      exact (labelPattern_independent μ f g a a hd).comp
        (measurable_const.mul measurable_id) (measurable_const.mul measurable_id))
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hh
  exact hh.trans (overlap_fraction_le m n hn)

/-- Convergence of the fractional target together with growing vertex orders
makes the random labelled statistic converge in mean square to that target. -/
theorem weightedPatternAverage_mean_square_tendsto {m : ℕ} {K : Type*}
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ∀ n, Fin (N n) → Measure K) [∀ n v, IsProbabilityMeasure (μ n v)]
    (w : ∀ n, (Fin m → Fin (N n)) → ℝ)
    (hw : ∀ n f, 0 ≤ w n f ∧ w n f ≤ 1) (a : Fin m → K) {b : ℝ}
    (hb : Tendsto (fun n => fractionalPatternAverage (μ n) (w n) a) atTop (𝓝 b)) :
    Tendsto (fun n => ∫ ω, (weightedPatternAverage (w n) a ω-b)^2 ∂Measure.pi (μ n))
      atTop (𝓝 0) := by
  let X := fun n => weightedPatternAverage (w n) a
  let A := fun n => fractionalPatternAverage (μ n) (w n) a
  have he : Tendsto (fun n => (m : ℝ)^2/(N n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
  have hpos := hN.eventually_gt_atTop 0
  have hmerr : Tendsto (fun n => |(∫ ω, X n ω ∂Measure.pi (μ n))-A n|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) _ he
    filter_upwards [hpos] with n hn
    exact weightedPatternAverage_mean_error (μ n) (w n) (hw n) a hn
  have hdiff : Tendsto (fun n => (∫ ω, X n ω ∂Measure.pi (μ n))-A n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hmerr
  have hm : Tendsto (fun n => ∫ ω, X n ω ∂Measure.pi (μ n)) atTop (𝓝 b) := by
    simpa only [A, sub_add_cancel, zero_add] using hdiff.add hb
  have hv : Tendsto (fun n => variance (X n) (Measure.pi (μ n))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => variance_nonneg _ _)) _ he
    filter_upwards [hpos] with n hn
    exact weightedPatternAverage_variance (μ n) (w n) (hw n) a hn
  exact mean_square_tendsto_of_mean_variance (fun n => Measure.pi (μ n)) X
    (fun n => weightedPatternAverage_memLp (μ n) (w n) (hw n) a) b hm hv

/-- One deterministic labelling at each order realizes every countably listed
finite pattern whose fractional target converges. -/
theorem exists_pattern_realization {K : Type*} [Nonempty K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ∀ n, Fin (N n) → Measure K) [∀ n v, IsProbabilityMeasure (μ n v)]
    (m : ℕ → ℕ) (w : ∀ n i, (Fin (m i) → Fin (N n)) → ℝ)
    (hw : ∀ n i f, 0 ≤ w n i f ∧ w n i f ≤ 1)
    (a : ∀ i, Fin (m i) → K) (b : ℕ → ℝ)
    (hb : ∀ i, Tendsto (fun n => fractionalPatternAverage (μ n) (w n i) (a i))
      atTop (𝓝 (b i))) :
    ∃ ω : ∀ n, Fin (N n) → K, ∀ i,
      Tendsto (fun n => weightedPatternAverage (w n i) (a i) (ω n)) atTop (𝓝 (b i)) := by
  apply exists_realization_of_mean_square (fun n => Measure.pi (μ n))
    (fun n i => weightedPatternAverage (w n i) (a i)) b
  · intro n i
    exact ((weightedPatternAverage_memLp (μ n) (w n i) (hw n i) (a i)).sub
      (memLp_const (b i))).integrable_sq
  · intro i
    exact weightedPatternAverage_mean_square_tendsto N hN μ (fun n => w n i)
      (fun n => hw n i) (a i) (hb i)

end HadwigerRamsey4Col.Realization
