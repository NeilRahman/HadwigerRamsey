import HadwigerRamsey4Col.RealizationDefinitions

open scoped BigOperators Topology Classical
open MeasureTheory Filter Finset Set

namespace HadwigerRamsey4Col.Realization

lemma labelPattern_eq_ite {I V K : Type*} [Fintype I]
    (f : I → V) (a : I → K) (ω : V → K) :
    labelPattern f a ω = if ω ∘ f = a then 1 else 0 := by
  by_cases h : ω ∘ f = a
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have he : ω (f i) = a i := congrFun h i
    simp [labelIndicator, he]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ω (f i) ≠ a i := by
      by_contra! hh
      exact h (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [labelIndicator, hi]

lemma finite_mark_expansion {I V K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (f : I → V) (ω : V → K) (g : (I → K) → ℝ) :
    g (ω ∘ f) = ∑ a : I → K, g a * labelPattern f a ω := by
  simp only [labelPattern_eq_ite]
  simp

lemma marked_integrand_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (A : Fin k → Set α)
    (hA : ∀ i, MeasurableSet (A i)) :
    Integrable (fun x : Fin P.1 → α =>
      (∏ u, (A (P.label u)).indicator (fun _ => (1 : ℝ)) (x u)) *
      ∏ e ∈ P.graph.edgeFinset,
        (W (P.colour e)).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) := by
  apply (Graphon.heterogeneous_integrand_integrable P.graph.edgeFinset
    (fun e => W (P.colour e))
    (fun e he => Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))).bdd_mul
  · apply Measurable.aestronglyMeasurable
    apply Finset.measurable_prod
    intro u hu
    exact (measurable_const.indicator (hA (P.label u))).comp (measurable_pi_apply u)
  · apply Eventually.of_forall
    intro x
    have hb (u : Fin P.1) : (A (P.label u)).indicator (fun _ => (1 : ℝ)) (x u) ∈ Icc (0 : ℝ) 1 := by
      by_cases hu : x u ∈ A (P.label u) <;> simp [hu]
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun u _ => (hb u).1))]
    exact Finset.prod_le_one (fun u _ => (hb u).1) (fun u _ => (hb u).2)

/-- Change only the required vertex labels in a test. -/
def withLabels {r k : ℕ} (P : Pattern r k) (a : Fin P.1 → Fin k) : Pattern r k :=
  ⟨P.1, P.graph, P.colour, a⟩

/-- Any finite function of vertex marks can be expanded into labelled tests. -/
theorem finite_density_mark_expansion {r k n : ℕ} (P : Pattern r k)
    (G : Fin r → SimpleGraph (Fin n)) (mark : Fin n → Fin k)
    (g : (Fin P.1 → Fin k) → ℝ) :
    (∑ f : Fin P.1 → Fin n, finitePatternWeight P G f * g (mark ∘ f)) / (n : ℝ)^P.1 =
      ∑ a : Fin P.1 → Fin k, g a * finitePatternDensity (withLabels P a) G mark := by
  simp_rw [finite_mark_expansion _ mark g, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  change (∑ f, finitePatternWeight P G f * (g a * labelPattern f a mark)) / (n : ℝ)^P.1 =
    g a * ((∑ f, finitePatternWeight P G f * labelPattern f a mark) / (n : ℝ)^P.1)
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  ring

/-- The same finite expansion for graphon integrals. -/
theorem graphon_density_mark_expansion {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (mark : α → Fin k) (hmark : Measurable mark)
    (g : (Fin P.1 → Fin k) → ℝ) :
    (∫ x : Fin P.1 → α,
      (∏ e ∈ P.graph.edgeFinset, (W (P.colour e)).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2)) * g (mark ∘ x)
      ∂Measure.pi (fun _ => μ)) =
      ∑ a : Fin P.1 → Fin k, g a *
        markedDensity (withLabels P a) W (fun i => mark ⁻¹' {i}) := by
  have heq (x : Fin P.1 → α) :
      (∏ e ∈ P.graph.edgeFinset, (W (P.colour e)).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2)) * g (mark ∘ x) =
      ∑ a : Fin P.1 → Fin k, g a *
        ((∏ u, (mark ⁻¹' {a u}).indicator (fun _ => (1 : ℝ)) (x u)) *
          ∏ e ∈ P.graph.edgeFinset, (W (P.colour e)).toAEEqFun
            (x (Quot.out e).1, x (Quot.out e).2)) := by
    rw [finite_mark_expansion x mark g, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hprod : labelPattern x a mark =
        ∏ u, (mark ⁻¹' {a u}).indicator (fun _ => (1 : ℝ)) (x u) := by
      apply Finset.prod_congr rfl
      intro u hu
      simp [labelIndicator, Set.indicator_apply]
    rw [hprod]
    ring
  simp_rw [heq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_const_mul]
    rfl
  · intro a ha
    exact (marked_integrand_integrable (withLabels P a) W (fun i => mark ⁻¹' {i})
      (fun i => hmark (measurableSet_singleton i))).const_mul (g a)

/-- Convergence of all marked tests controls every fixed finite coefficient
function of the marks as well. -/
theorem polynomial_density_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (marks : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (mark : α → Fin k) (hmark : Measurable mark)
    (h : ∀ Q : Pattern r k, Tendsto (fun n => finitePatternDensity Q (G n) (marks n))
      atTop (𝓝 (markedDensity Q W (fun i => mark ⁻¹' {i}))))
    (g : (Fin P.1 → Fin k) → ℝ) :
    Tendsto (fun n => (∑ f : Fin P.1 → Fin (N n),
      finitePatternWeight P (G n) f * g (marks n ∘ f)) / (N n : ℝ)^P.1)
      atTop (𝓝 (∫ x : Fin P.1 → α,
        (∏ e ∈ P.graph.edgeFinset, (W (P.colour e)).toAEEqFun
          (x (Quot.out e).1,x (Quot.out e).2)) * g (mark ∘ x)
        ∂Measure.pi (fun _ => μ))) := by
  simp_rw [finite_density_mark_expansion, graphon_density_mark_expansion P W mark hmark]
  exact tendsto_finsetSum univ (fun a _ => (h (withLabels P a)).const_mul (g a))

end HadwigerRamsey4Col.Realization
