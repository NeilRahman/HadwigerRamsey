import ComponentTransfer.RealizationWeightedCounting
import ComponentTransfer.RealizationProbabilityLabels

open scoped BigOperators Classical Topology
open MeasureTheory Filter Finset Set

namespace ComponentTransfer.Realization

/-- Finite coloured test graphs with a specified partition class at every vertex. -/
abbrev Pattern (r k : ℕ) :=
  Σ m : ℕ, SimpleGraph (Fin m) × (Sym2 (Fin m) → Fin r) × (Fin m → Fin k)

namespace Pattern
variable {r k : ℕ}
def graph (P : Pattern r k) : SimpleGraph (Fin P.1) := P.2.1
def colour (P : Pattern r k) : Sym2 (Fin P.1) → Fin r := P.2.2.1
def label (P : Pattern r k) : Fin P.1 → Fin k := P.2.2.2
end Pattern

instance pattern_countable (r k : ℕ) : Countable (Pattern r k) := by
  unfold Pattern
  infer_instance

/-- The edge contribution of a test map to a finite coloured graph. -/
noncomputable def finitePatternWeight {r k n : ℕ} (P : Pattern r k)
    (G : Fin r → SimpleGraph (Fin n)) (f : Fin P.1 → Fin n) : ℝ :=
  ∏ e ∈ P.graph.edgeFinset,
    Graphon.adjIndicator (G (P.colour e)) (f (Quot.out e).1) (f (Quot.out e).2)

lemma finitePatternWeight_bounds {r k n : ℕ} (P : Pattern r k)
    (G : Fin r → SimpleGraph (Fin n)) (f : Fin P.1 → Fin n) :
    0 ≤ finitePatternWeight P G f ∧ finitePatternWeight P G f ≤ 1 := by
  have hb (e : Sym2 (Fin P.1)) :
      Graphon.adjIndicator (G (P.colour e)) (f (Quot.out e).1) (f (Quot.out e).2) ∈ Set.Icc (0 : ℝ) 1 := by
    unfold Graphon.adjIndicator
    split_ifs <;> norm_num
  unfold finitePatternWeight
  constructor
  · exact prod_nonneg (fun e _ => (hb e).1)
  · exact prod_le_one (fun e _ => (hb e).1)
      (fun e _ => (hb e).2)

/-- The normalized number of maps preserving the test edges and vertex labels. -/
noncomputable def finitePatternDensity {r k n : ℕ} (P : Pattern r k)
    (G : Fin r → SimpleGraph (Fin n)) (label : Fin n → Fin k) : ℝ :=
  (∑ f : Fin P.1 → Fin n, finitePatternWeight P G f * labelPattern f P.label label) /
    (n : ℝ)^P.1

/-- Weighted homomorphism density in a coloured graphon with a measurable marking. -/
noncomputable def markedDensity {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r k : ℕ} (P : Pattern r k) (W : Fin r → Graphon α μ) (A : Fin k → Set α) : ℝ :=
  ∫ x : Fin P.1 → α,
    (∏ u, (A (P.label u)).indicator (fun _ => (1 : ℝ)) (x u)) *
    ∏ e ∈ P.graph.edgeFinset,
      (W (P.colour e)).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    ∂Measure.pi (fun _ => μ)

/-- If a required class is null, every marked density for that test is zero. -/
theorem markedDensity_zero_of_null {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (A : Fin k → Set α)
    (u : Fin P.1) (hu : μ (A (P.label u)) = 0) : markedDensity P W A = 0 := by
  have hnull : ∀ᵐ x ∂μ, x ∉ A (P.label u) := by
    rw [ae_iff]
    simpa using hu
  have hp := (measurePreserving_eval (fun _ : Fin P.1 => μ) u).quasiMeasurePreserving.ae hnull
  apply integral_eq_zero_of_ae
  filter_upwards [hp] with x hx
  have hz : ∏ v : Fin P.1, (A (P.label v)).indicator (fun _ => (1 : ℝ)) (x v) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    exact Set.indicator_of_notMem hx _
  simp only [hz, zero_mul, Pi.zero_apply]

/-- Common cut-norm convergence implies convergence of every marked coloured test.
Null partition classes are allowed, so this applies to arbitrary refinements. -/
theorem markedDensity_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (U : ℕ → Fin r → Graphon α μ) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hcut : ∀ c, Tendsto (fun n => Graphon.cutNormDiff (U n c) (W c)) atTop (𝓝 0)) :
    Tendsto (fun n => markedDensity P (U n) A) atTop (𝓝 (markedDensity P W A)) := by
  by_cases hpos : ∀ u : Fin P.1, 0 < μ.real (A (P.label u))
  · have hbound (n : ℕ) := vertex_weighted_counting P.graph.edgeFinset
      (fun e => U n (P.colour e)) (fun e => W (P.colour e))
      (fun e he => Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
      (fun u => A (P.label u)) (fun u => hA (P.label u)) hpos
    have hlim : Tendsto (fun n => (∑ e ∈ P.graph.edgeFinset,
        Graphon.cutNormDiff (U n (P.colour e)) (W (P.colour e))) /
        ∏ u, μ.real (A (P.label u))) atTop (𝓝 0) := by
      have h := (tendsto_finsetSum P.graph.edgeFinset (fun e _ => hcut (P.colour e))).div_const
        (∏ u, μ.real (A (P.label u)))
      simpa using h
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using squeeze_zero
      (fun n => abs_nonneg (markedDensity P (U n) A - markedDensity P W A)) hbound hlim
  · push Not at hpos
    obtain ⟨u, hu⟩ := hpos
    have hz : μ (A (P.label u)) = 0 := (measureReal_eq_zero_iff (μ := μ)).mp
      (le_antisymm hu measureReal_nonneg)
    simp only [markedDensity_zero_of_null P _ A u hz]
    exact tendsto_const_nhds

end ComponentTransfer.Realization
