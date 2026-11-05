import HadwigerRamsey4Col.RealizationResidual
import HadwigerRamsey4Col.RealizationResidualBound
import HadwigerRamsey4Col.RealizationConvergenceCost
import HadwigerRamsey4Col.RealizationCells
import HadwigerRamsey4Col.RealizationConvergenceC4

open scoped BigOperators Classical Topology
open MeasureTheory Set Finset Filter

set_option backward.isDefEq.respectTransparency false

namespace HadwigerRamsey4Col.Realization

def c4Edges : Finset (Sym2 (Fin 4)) := {s(0,2),s(1,2),s(0,3),s(1,3)}

def c4Graph : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet c4Edges

lemma c4Graph_edges : c4Graph.edgeFinset = c4Edges := by
  ext e
  induction e using Sym2.ind with | _ a b =>
    fin_cases a <;> fin_cases b <;>
      simp [c4Graph, c4Edges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]

lemma sym2_out_apply {V : Type*} (K : V → V → ℝ) (hK : ∀ i j, K i j = K j i)
    (a b : V) : K (Quot.out s(a,b)).1 (Quot.out s(a,b)).2 = K a b := by
  have h : s((Quot.out s(a,b)).1,(Quot.out s(a,b)).2) = s(a,b) := Quot.out_eq _
  rcases Sym2.eq_iff.mp h with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2,hK]

lemma c4_product {V : Type*} (K : V → V → ℝ) (hK : ∀ i j, K i j = K j i)
    (f : Fin 4 → V) :
    (∏ e ∈ c4Edges, K (f (Quot.out e).1) (f (Quot.out e).2)) =
      K (f 2) (f 0) * K (f 2) (f 1) * K (f 3) (f 0) * K (f 3) (f 1) := by
  have hk (i j : Fin 4) := sym2_out_apply (fun u v => K (f u) (f v)) (fun u v => hK _ _) i j
  unfold c4Edges
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [hk]
  rw [hK (f 0) (f 2),hK (f 1) (f 2),hK (f 0) (f 3),hK (f 1) (f 3)]
  ring

/-- A monochromatic four-cycle test; labels are irrelevant after polynomial expansion. -/
abbrev c4Pattern {r k : ℕ} (c : Fin r) (a : Fin k) : Pattern r k :=
  ⟨4,c4Graph,fun _ => c,fun _ => a⟩

noncomputable def residualC4Integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (W : Graphon α μ) {k : ℕ} (B : Fin k → Fin k → ℝ) (mark : α → Fin k) : ℝ :=
  ∫ x : Fin 4 → α, ∏ e ∈ c4Edges,
    (W.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
      B (mark (x (Quot.out e).1)) (mark (x (Quot.out e).2))) ∂Measure.pi (fun _ => μ)

lemma adjacencyMatrix_symm {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    Graphon.adjIndicator G i j = Graphon.adjIndicator G j i := by
  simp only [Graphon.adjIndicator, G.adj_comm]

lemma adjacencyMatrix_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    Graphon.adjIndicator G i j ∈ Icc (0 : ℝ) 1 := by
  unfold Graphon.adjIndicator
  split_ifs <;> norm_num

/-- All marked test limits give convergence of the signed residual four-cycle. -/
theorem finiteC4_tendsto_of_patterns {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r) (a : Fin k)
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (marks : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (mark : α → Fin k) (hmark : Measurable mark)
    (h : ∀ Q : Pattern r k, Tendsto (fun n => finitePatternDensity Q (G n) (marks n))
      atTop (𝓝 (markedDensity Q W (fun i => mark ⁻¹' {i}))))
    (B : Fin k → Fin k → ℝ) (hBsymm : ∀ i j, B i j = B j i) :
    Tendsto (fun n => finiteC4 (fun i j => Graphon.adjIndicator (G n c) i j -
        B (marks n i) (marks n j))) atTop (𝓝 (residualC4Integral (W c) B mark)) := by
  have ht := residual_density_tendsto (c4Pattern c a) N G marks W mark hmark h (fun _ => B)
  have hfinite (n : ℕ) :
      finiteC4 (fun i j => Graphon.adjIndicator (G n c) i j - B (marks n i) (marks n j)) =
      (∑ f : Fin 4 → Fin (N n), ∏ e ∈ c4Edges,
        (Graphon.adjIndicator (G n c) (f (Quot.out e).1) (f (Quot.out e).2) -
          B (marks n (f (Quot.out e).1)) (marks n (f (Quot.out e).2)))) / (N n : ℝ)^4 := by
    rw [finiteC4_eq_fin4_sum]
    simp only [Fintype.card_fin]
    congr 1
    apply Finset.sum_congr rfl
    intro f hf
    symm
    exact c4_product (fun i j => Graphon.adjIndicator (G n c) i j - B (marks n i) (marks n j))
      (by intro i j; rw [adjacencyMatrix_symm, hBsymm]) f
  simp_rw [hfinite]
  simpa only [c4Pattern, Pattern.graph, Pattern.colour, c4Graph_edges, residualC4Integral] using ht

/-- The limiting signed four-cycle is at most eight times the approximation
cut error. The approximating matrix may have arbitrary null cells. -/
theorem residualC4Integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (W : Graphon α μ) {k : ℕ}
    (B : Fin k → Fin k → ℝ) (hBsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, B i j ∈ Icc (0 : ℝ) 1) (mark : α → Fin k) (hmark : Measurable mark) :
    residualC4Integral W B mark ≤
      8 * Graphon.cutNormDiff W (markedGraphon B hBsymm hB mark hmark) := by
  let Q := markedGraphon (μ := μ) B hBsymm hB mark hmark
  have hedge (e) (he : e ∈ c4Edges) : (Quot.out e).1 ≠ (Quot.out e).2 := by
    apply Graphon.edge_out_ne (F := c4Graph)
    apply (SimpleGraph.mem_edgeFinset (G := c4Graph)).mp
    rwa [c4Graph_edges]
  have hraw : ∀ᵐ x : Fin 4 → α ∂Measure.pi (fun _ => μ), ∀ e ∈ c4Edges,
      Q.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) =
        B (mark (x (Quot.out e).1)) (mark (x (Quot.out e).2)) := by
    apply (Filter.eventually_all_finite c4Edges.finite_toSet).mpr
    intro e he
    exact (pair_measurePreserving (μ := μ) (Quot.out e).1 (Quot.out e).2 (hedge e he)).quasiMeasurePreserving.ae
      (markedGraphon_ae B hBsymm hB mark hmark)
  have hIntegral : residualC4Integral W B mark =
      ∫ x : Fin 4 → α, ∏ e ∈ c4Edges,
        (W.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
          Q.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2)) ∂Measure.pi (fun _ => μ) := by
    apply integral_congr_ae
    filter_upwards [hraw] with x hx
    apply Finset.prod_congr rfl
    intro e he
    rw [hx e he]
  let e₀ : Sym2 (Fin 4) := s(0,2)
  have he₀ : e₀ ∈ c4Edges := by simp [e₀,c4Edges]
  have hb := residual_product_integral_le (fun _ : Sym2 (Fin 4) => W)
    (fun _ : Sym2 (Fin 4) => Q) (c4Edges.erase e₀) e₀ (Finset.notMem_erase _ _)
    (fun e he => hedge e (Finset.mem_of_mem_erase he)) (hedge e₀ he₀)
  have heq (x : Fin 4 → α) :
      (∏ e ∈ c4Edges, (W.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
          Q.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))) =
      (∏ e ∈ c4Edges.erase e₀, (W.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2) -
          Q.toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))) *
        (W.toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2) -
          Q.toAEEqFun (x (Quot.out e₀).1,x (Quot.out e₀).2)) := by
    exact (Finset.prod_erase_mul _ _ he₀).symm
  have hcard : (c4Edges.erase e₀).card = 3 := by
    decide
  rw [hcard] at hb
  norm_num only [Nat.reducePow] at hb
  rw [hIntegral]
  simp_rw [heq]
  exact (le_abs_self _).trans (by simpa using hb)

end HadwigerRamsey4Col.Realization
