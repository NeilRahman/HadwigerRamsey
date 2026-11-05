import HadwigerRamsey4Col.RealizationPolynomial
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

open scoped BigOperators Topology Classical
open MeasureTheory Filter Finset Set

namespace HadwigerRamsey4Col.Realization

abbrev withoutEdges {r k : ℕ} (P : Pattern r k) (s : Finset (Sym2 (Fin P.1))) : Pattern r k :=
  ⟨P.1, P.graph.deleteEdges s, P.colour, P.label⟩

lemma withoutEdges_edgeFinset {r k : ℕ} (P : Pattern r k) (s : Finset (Sym2 (Fin P.1))) :
    (withoutEdges P s).graph.edgeFinset = P.graph.edgeFinset \ s := by
  exact @SimpleGraph.edgeFinset_deleteEdges (Fin P.1) P.graph _ _ s
    (inferInstance : Fintype (withoutEdges P s).graph.edgeSet)


lemma polynomial_integrand_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (mark : α → Fin k) (hmark : Measurable mark)
    (g : (Fin P.1 → Fin k) → ℝ) :
    Integrable (fun x : Fin P.1 → α =>
      (∏ e ∈ P.graph.edgeFinset, (W (P.colour e)).toAEEqFun
        (x (Quot.out e).1, x (Quot.out e).2)) * g (mark ∘ x))
      (Measure.pi (fun _ => μ)) := by
  apply (Graphon.heterogeneous_integrand_integrable P.graph.edgeFinset
    (fun e => W (P.colour e))
    (fun e he => Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))).mul_bdd
  · exact ((Measurable.of_discrete : Measurable g).comp
      (measurable_pi_lambda _ (fun i => hmark.comp (measurable_pi_apply i)))).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => Finset.single_le_sum
      (fun i _ => norm_nonneg (g i)) (Finset.mem_univ (mark ∘ x)))

/-- Residual products are polynomial combinations of marked graph tests. -/
theorem residual_density_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (marks : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (mark : α → Fin k) (hmark : Measurable mark)
    (h : ∀ Q : Pattern r k, Tendsto (fun n => finitePatternDensity Q (G n) (marks n))
      atTop (𝓝 (markedDensity Q W (fun i => mark ⁻¹' {i}))))
    (B : Fin r → Fin k → Fin k → ℝ) :
    Tendsto (fun n => (∑ f : Fin P.1 → Fin (N n),
      ∏ e ∈ P.graph.edgeFinset,
        (Graphon.adjIndicator (G n (P.colour e)) (f (Quot.out e).1) (f (Quot.out e).2) -
         B (P.colour e) (marks n (f (Quot.out e).1)) (marks n (f (Quot.out e).2)))) /
         (N n : ℝ)^P.1)
      atTop (𝓝 (∫ x : Fin P.1 → α,
        ∏ e ∈ P.graph.edgeFinset,
          ((W (P.colour e)).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
           B (P.colour e) (mark (x (Quot.out e).1)) (mark (x (Quot.out e).2)))
        ∂Measure.pi (fun _ => μ))) := by
  let coeff (s : Finset (Sym2 (Fin P.1))) (a : Fin P.1 → Fin k) : ℝ :=
    (-1)^s.card * ∏ e ∈ s, B (P.colour e) (a (Quot.out e).1) (a (Quot.out e).2)
  have hterm (s : Finset (Sym2 (Fin P.1))) :=
    polynomial_density_tendsto (withoutEdges P s) N G marks W mark hmark h (coeff s)
  have hlim := tendsto_finsetSum P.graph.edgeFinset.powerset (fun s _ => hterm s)
  have finite_eq (n : ℕ) :
      (∑ f : Fin P.1 → Fin (N n),
        ∏ e ∈ P.graph.edgeFinset,
          (Graphon.adjIndicator (G n (P.colour e)) (f (Quot.out e).1) (f (Quot.out e).2) -
            B (P.colour e) (marks n (f (Quot.out e).1)) (marks n (f (Quot.out e).2)))) /
          (N n : ℝ)^P.1 =
      ∑ s ∈ P.graph.edgeFinset.powerset,
        (∑ f : Fin P.1 → Fin (N n), finitePatternWeight (withoutEdges P s) (G n) f *
          coeff s (marks n ∘ f)) / (N n : ℝ)^P.1 := by
    simp_rw [Finset.prod_sub]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    apply Fintype.sum_congr
    intro f
    unfold finitePatternWeight
    rw [withoutEdges_edgeFinset]
    change _ = (∏ e ∈ P.graph.edgeFinset \ s,
      Graphon.adjIndicator (G n (P.colour e)) (f (Quot.out e).1) (f (Quot.out e).2)) *
      ((-1)^s.card * ∏ e ∈ s, B (P.colour e) (marks n (f (Quot.out e).1))
        (marks n (f (Quot.out e).2)))
    ring
  have integral_eq :
      (∫ x : Fin P.1 → α, ∏ e ∈ P.graph.edgeFinset,
        ((W (P.colour e)).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
          B (P.colour e) (mark (x (Quot.out e).1)) (mark (x (Quot.out e).2)))
        ∂Measure.pi (fun _ => μ)) =
      ∑ s ∈ P.graph.edgeFinset.powerset,
        ∫ x : Fin P.1 → α,
          (∏ e ∈ (withoutEdges P s).graph.edgeFinset,
            (W ((withoutEdges P s).colour e)).toAEEqFun
              (x (Quot.out e).1,x (Quot.out e).2)) * coeff s (mark ∘ x)
          ∂Measure.pi (fun _ => μ) := by
    have heq (x : Fin P.1 → α) :
        (∏ e ∈ P.graph.edgeFinset,
          ((W (P.colour e)).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
            B (P.colour e) (mark (x (Quot.out e).1)) (mark (x (Quot.out e).2)))) =
        ∑ s ∈ P.graph.edgeFinset.powerset,
          (∏ e ∈ (withoutEdges P s).graph.edgeFinset,
            (W ((withoutEdges P s).colour e)).toAEEqFun
              (x (Quot.out e).1,x (Quot.out e).2)) * coeff s (mark ∘ x) := by
      rw [Finset.prod_sub]
      apply Finset.sum_congr rfl
      intro s hs
      rw [withoutEdges_edgeFinset]
      change _ = (∏ e ∈ P.graph.edgeFinset \ s,
        (W (P.colour e)).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2)) *
        ((-1)^s.card * ∏ e ∈ s, B (P.colour e) (mark (x (Quot.out e).1))
          (mark (x (Quot.out e).2)))
      ring
    simp_rw [heq]
    exact integral_finsetSum _ (fun s _ =>
      polynomial_integrand_integrable (withoutEdges P s) W mark hmark (coeff s))
  simp_rw [finite_eq, integral_eq]
  exact hlim

end HadwigerRamsey4Col.Realization
