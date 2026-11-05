import ComponentTransfer.Realization
import HadwigerRamsey.ThomasonUpper.Density

open scoped BigOperators Topology Classical
open MeasureTheory Filter Finset Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

namespace ComponentTransfer.Realization

/-- A single labelled vertex, used to test partition sizes. -/
abbrev vertexPattern {r k : ℕ} (c : Fin r) (i : Fin k) : Pattern r k :=
  ⟨1, ⊥, fun _ => c, fun _ => i⟩

/-- One coloured edge with specified classes for its two endpoints. -/
abbrev edgePattern {r k : ℕ} (c : Fin r) (i j : Fin k) : Pattern r k :=
  ⟨2, ⊤, fun _ => c, ![i,j]⟩

lemma edgeFinset_fin_two_top :
    (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0,1)} := by
  ext e
  induction e using Sym2.ind with
  | _ u v => fin_cases u <;> fin_cases v <;> simp

lemma edge01_out :
    ((Quot.out (s(0,1) : Sym2 (Fin 2))).1 = 0 ∧
      (Quot.out (s(0,1) : Sym2 (Fin 2))).2 = 1) ∨
    ((Quot.out (s(0,1) : Sym2 (Fin 2))).1 = 1 ∧
      (Quot.out (s(0,1) : Sym2 (Fin 2))).2 = 0) := by
  apply Sym2.eq_iff.mp
  exact Quot.out_eq _

lemma vertexPattern_edgeFinset {r k : ℕ} (c : Fin r) (i : Fin k) :
    (vertexPattern c i).graph.edgeFinset = ∅ := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  simp [vertexPattern, Pattern.graph]

lemma edgePattern_edgeFinset {r k : ℕ} (c : Fin r) (i j : Fin k) :
    (edgePattern c i j).graph.edgeFinset = {s(0,1)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  change e ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet ↔ _
  rw [← SimpleGraph.mem_edgeFinset, edgeFinset_fin_two_top]

lemma finitePatternWeight_vertex {r k n : ℕ} (c : Fin r) (i : Fin k)
    (G : Fin r → SimpleGraph (Fin n)) (f : Fin 1 → Fin n) :
    finitePatternWeight (vertexPattern c i) G f = 1 := by
  unfold finitePatternWeight
  rw [vertexPattern_edgeFinset, Finset.prod_empty]

lemma finitePatternWeight_edge {r k n : ℕ} (c : Fin r) (i j : Fin k)
    (G : Fin r → SimpleGraph (Fin n)) (f : Fin 2 → Fin n) :
    finitePatternWeight (edgePattern c i j) G f =
      Graphon.adjIndicator (G c) (f 0) (f 1) := by
  unfold finitePatternWeight
  rw [edgePattern_edgeFinset, Finset.prod_singleton]
  change Graphon.adjIndicator (G c) (f (Quot.out (s(0,1) : Sym2 (Fin 2))).1)
    (f (Quot.out (s(0,1) : Sym2 (Fin 2))).2) = _
  rcases edge01_out with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb]
    simp only [Graphon.adjIndicator, (G c).adj_comm]

lemma finitePatternDensity_vertex {r k n : ℕ} (c : Fin r) (i : Fin k)
    (G : Fin r → SimpleGraph (Fin n)) (τ : Fin n → Fin k) :
    finitePatternDensity (vertexPattern c i) G τ = classMass τ i := by
  change (∑ f : Fin 1 → Fin n, finitePatternWeight (vertexPattern c i) G f *
    labelPattern f (fun _ => i) τ) / (n : ℝ)^1 = _
  simp only [finitePatternWeight_vertex, one_mul, labelPattern, Fin.prod_univ_one, pow_one]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n))
    (fun f => labelIndicator i (τ (f 0))) (fun v => labelIndicator i (τ v))
    (by intro f; rfl)]
  simp only [labelIndicator, Set.indicator_apply, Set.mem_singleton_iff]
  rw [Finset.sum_boole]
  rfl

lemma finitePatternDensity_edge {r k n : ℕ} (c : Fin r) (i j : Fin k)
    (G : Fin r → SimpleGraph (Fin n)) (τ : Fin n → Fin k) :
    finitePatternDensity (edgePattern c i j) G τ =
      ((G c).interedges (classVertices τ i) (classVertices τ j)).card / (n : ℝ)^2 := by
  change (∑ f : Fin 2 → Fin n, finitePatternWeight (edgePattern c i j) G f *
    labelPattern f ![i,j] τ) / (n : ℝ)^2 = _
  simp only [finitePatternWeight_edge, labelPattern, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsum : (∑ f : Fin 2 → Fin n,
      Graphon.adjIndicator (G c) (f 0) (f 1) *
        (labelIndicator i (τ (f 0)) * labelIndicator j (τ (f 1)))) =
      ∑ p : Fin n × Fin n,
        if p ∈ (G c).interedges (classVertices τ i) (classVertices τ j)
          then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv ((MeasurableEquiv.piFinTwo (fun _ => Fin n)).toEquiv)
    intro f
    simp only [SimpleGraph.mem_interedges_iff,
      classVertices, mem_filter, Finset.mem_univ, true_and, labelIndicator,
      Set.indicator_apply, Set.mem_singleton_iff, Graphon.adjIndicator]
    split_ifs <;> simp_all
  rw [hsum, Finset.sum_boole]
  simp

lemma markedDensity_vertex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r) (i : Fin k)
    (W : Fin r → Graphon α μ) (A : Fin k → Set α) (hA : MeasurableSet (A i)) :
    markedDensity (vertexPattern c i) W A = μ.real (A i) := by
  unfold markedDensity
  rw [vertexPattern_edgeFinset]
  simp only [Finset.prod_empty, mul_one]
  change (∫ x : Fin 1 → α, (∏ u, (A i).indicator (fun _ => (1 : ℝ)) (x u))
      ∂Measure.pi (fun _ => μ)) = _
  simp only [Fin.prod_univ_one]
  exact ((measurePreserving_funUnique μ (Fin 1)).integral_comp'
    ((A i).indicator (fun _ => (1 : ℝ)))).trans (integral_indicator_one hA)

lemma markedDensity_edge {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r) (i j : Fin k)
    (W : Fin r → Graphon α μ) (A : Fin k → Set α) :
    markedDensity (edgePattern c i j) W A =
      ∫ p : α × α, (A i).indicator (fun _ => (1 : ℝ)) p.1 *
        (A j).indicator (fun _ => (1 : ℝ)) p.2 * (W c).toAEEqFun p ∂μ.prod μ := by
  unfold markedDensity
  rw [edgePattern_edgeFinset]
  change (∫ x : Fin 2 → α, (∏ u, (A (![i,j] u)).indicator (fun _ => (1 : ℝ)) (x u)) *
    (∏ e ∈ ({s(0,1)} : Finset (Sym2 (Fin 2))),
      (W c).toAEEqFun (x (Quot.out e).1,x (Quot.out e).2))
        ∂Measure.pi (fun _ => μ)) = _
  simp only [Finset.prod_singleton]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsym := (measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).quasiMeasurePreserving.ae
    (W c).symm_ae
  have heq : (fun x : Fin 2 → α =>
      (A i).indicator (fun _ => (1 : ℝ)) (x 0) *
      (A j).indicator (fun _ => (1 : ℝ)) (x 1) *
      (W c).toAEEqFun (x (Quot.out (s(0,1) : Sym2 (Fin 2))).1,
        x (Quot.out (s(0,1) : Sym2 (Fin 2))).2)) =ᵐ[Measure.pi (fun _ => μ)]
      (fun x : Fin 2 → α => (A i).indicator (fun _ => (1 : ℝ)) (x 0) *
        (A j).indicator (fun _ => (1 : ℝ)) (x 1) * (W c).toAEEqFun (x 0,x 1)) := by
    filter_upwards [hsym] with x hx
    rcases edge01_out with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb]
    · rw [ha,hb]
      rw [show (W c).toAEEqFun (x 1,x 0) = (W c).toAEEqFun (x 0,x 1) from hx]
  rw [integral_congr_ae heq]
  exact (measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).integral_comp'
    (fun p : α × α => (A i).indicator (fun _ => (1 : ℝ)) p.1 *
      (A j).indicator (fun _ => (1 : ℝ)) p.2 * (W c).toAEEqFun p)

lemma indicator_rectangle_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : α × α → ℝ) :
    (∫ p : α × α, A.indicator (fun _ => (1 : ℝ)) p.1 *
      B.indicator (fun _ => (1 : ℝ)) p.2 * f p ∂μ.prod μ) =
      ∫ p in A ×ˢ B, f p ∂μ.prod μ := by
  have heq : (fun p : α × α => A.indicator (fun _ => (1 : ℝ)) p.1 *
      B.indicator (fun _ => (1 : ℝ)) p.2 * f p) = (A ×ˢ B).indicator f := by
    funext p
    by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;>
      simp [ha,hb,Set.mem_prod]
  rw [heq, integral_indicator (hA.prod hB)]

lemma markedDensity_edge_eq_rectIntegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {r k : ℕ}
    (c : Fin r) (i j : Fin k) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i)) :
    markedDensity (edgePattern c i j) W A =
      (W c).toSymmKernel.rectIntegral (A i) (A j) := by
  rw [markedDensity_edge, indicator_rectangle_integral μ _ _ (hA i) (hA j)]
  rfl

/-- Partition sizes are among the finite marked test statistics. -/
theorem classMass_tendsto_of_patterns {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r)
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W A))) (i : Fin k) :
    Tendsto (fun n => classMass (τ n) i) atTop (𝓝 (μ.real (A i))) := by
  simpa only [finitePatternDensity_vertex, markedDensity_vertex c i W A (hA i)]
    using htests (vertexPattern c i)

/-- Positive limiting masses imply that each class grows without bound. -/
theorem classVertices_card_tendsto {k : ℕ} (N : ℕ → ℕ)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (τ : ∀ n, Fin (N n) → Fin k) (i : Fin k) {a : ℝ} (ha : 0 < a)
    (hmass : Tendsto (fun n => classMass (τ n) i) atTop (𝓝 a)) :
    Tendsto (fun n => ((classVertices (τ n) i).card : ℝ)) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop.comp hN).atTop_mul_pos ha hmass
  apply h.congr'
  filter_upwards [] with n
  have hn : (N n : ℝ) ≠ 0 := by exact_mod_cast (hNpos n).ne'
  dsimp [classMass, classVertices, Function.comp_def]
  field_simp

lemma edgeDensity_eq_normalized_interedges {n k : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (τ : Fin n → Fin k) (i j : Fin k)
    (hi : 0 < (classVertices τ i).card) (hj : 0 < (classVertices τ j).card) :
    (G.edgeDensity (classVertices τ i) (classVertices τ j) : ℝ) =
      (((G.interedges (classVertices τ i) (classVertices τ j)).card : ℝ) / (n : ℝ)^2) /
        (classMass τ i * classMass τ j) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hi' : ((classVertices τ i).card : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have hj' : ((classVertices τ j).card : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  change _ = _ / (((classVertices τ i).card / (n : ℝ)) *
    ((classVertices τ j).card / (n : ℝ)))
  simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  field_simp

lemma internalDensity_eq_normalized_interedges {n k : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (τ : Fin n → Fin k) (i : Fin k)
    (hi : 2 ≤ (classVertices τ i).card) :
    internalDensity G (classVertices τ i) =
      (((G.interedges (classVertices τ i) (classVertices τ i)).card : ℝ) / (n : ℝ)^2) /
        (classMass τ i * (classMass τ i - 1/(n : ℝ))) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hiR : (2 : ℝ) ≤ (classVertices τ i).card := by exact_mod_cast hi
  have hi' : ((classVertices τ i).card : ℝ) ≠ 0 := by linarith
  have hi1 : ((classVertices τ i).card : ℝ) - 1 ≠ 0 := by linarith
  change _ = _ / (((classVertices τ i).card / (n : ℝ)) *
    ((classVertices τ i).card / (n : ℝ) - 1/(n : ℝ)))
  rw [card_internal_interedges]
  simp only [internalDensity, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two]
  field_simp

/-- The diagonal uses the ordinary unordered-edge normalization. Its finite
size correction tends to one because each positive-mass class grows. -/
theorem blockDensity_tendsto_of_patterns {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hpos : ∀ i, 0 < μ.real (A i))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W A))) (c : Fin r) (i j : Fin k) :
    Tendsto (fun n => blockDensity (G n c) (τ n) i j) atTop
      (𝓝 ((∫ p : α × α, (A i).indicator (fun _ => (1 : ℝ)) p.1 *
        (A j).indicator (fun _ => (1 : ℝ)) p.2 * (W c).toAEEqFun p ∂μ.prod μ) /
          (μ.real (A i) * μ.real (A j)))) := by
  have hm (i : Fin k) := classMass_tendsto_of_patterns c N G τ W A hA htests i
  have hs (i : Fin k) := classVertices_card_tendsto N hNpos hN τ i (hpos i) (hm i)
  have he := htests (edgePattern c i j)
  simp only [finitePatternDensity_edge, markedDensity_edge] at he
  by_cases hij : i = j
  · subst j
    have hinv : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp hN)
    have hd := (hm i).mul ((hm i).sub hinv)
    simp only [sub_zero] at hd
    have h := he.div hd (mul_ne_zero (hpos i).ne' (hpos i).ne')
    apply h.congr'
    filter_upwards [(hs i).eventually_ge_atTop 2] with n hn
    have hn' : 2 ≤ (classVertices (τ n) i).card := by exact_mod_cast hn
    simp only [blockDensity, ite_true]
    exact (internalDensity_eq_normalized_interedges (hNpos n) (G n c) (τ n) i hn').symm
  · have h := he.div ((hm i).mul (hm j))
      (mul_ne_zero (hpos i).ne' (hpos j).ne')
    apply h.congr'
    filter_upwards [(hs i).eventually_ge_atTop 1, (hs j).eventually_ge_atTop 1] with n hi hj
    have hi' : 0 < (classVertices (τ n) i).card := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hi)
    have hj' : 0 < (classVertices (τ n) j).card := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hj)
    simp only [blockDensity, if_neg hij]
    exact (edgeDensity_eq_normalized_interedges (hNpos n) (G n c) (τ n) i j hi' hj').symm

/-- Edge densities converge to the normalized graphon rectangle integrals. -/
theorem blockDensity_tendsto_rectIntegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hpos : ∀ i, 0 < μ.real (A i))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W A))) (c : Fin r) (i j : Fin k) :
    Tendsto (fun n => blockDensity (G n c) (τ n) i j) atTop
      (𝓝 ((W c).toSymmKernel.rectIntegral (A i) (A j) /
        (μ.real (A i) * μ.real (A j)))) := by
  have h := blockDensity_tendsto_of_patterns N hNpos hN G τ W A hA hpos htests c i j
  rw [indicator_rectangle_integral μ _ _ (hA i) (hA j)] at h
  exact h

lemma exists_positive_order_tail (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∃ d : ℕ, ∀ n : ℕ, 0 < N (n+d) := by
  obtain ⟨d,hd⟩ := eventually_atTop.mp (hN.eventually_gt_atTop 0)
  exact ⟨d,fun n => hd (n+d) (Nat.le_add_left d n)⟩

/-- Finitely many empty initial graphs do not affect growth of a positive-mass class. -/
theorem classVertices_card_tendsto_of_order_tendsto {k : ℕ} (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (τ : ∀ n, Fin (N n) → Fin k)
    (i : Fin k) {a : ℝ} (ha : 0 < a)
    (hmass : Tendsto (fun n => classMass (τ n) i) atTop (𝓝 a)) :
    Tendsto (fun n => ((classVertices (τ n) i).card : ℝ)) atTop atTop := by
  obtain ⟨d,hd⟩ := exists_positive_order_tail N hN
  apply (tendsto_add_atTop_iff_nat d).mp
  exact classVertices_card_tendsto (fun n => N (n+d)) hd
    (hN.comp (tendsto_add_atTop_nat d)) (fun n => τ (n+d)) i ha
    (hmass.comp (tendsto_add_atTop_nat d))

/-- Ordinary part densities need only diverging graph orders; initial empty
graphs are harmless because convergence depends on a tail. -/
theorem blockDensity_tendsto_rectIntegral_of_order_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hpos : ∀ i, 0 < μ.real (A i))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W A))) (c : Fin r) (i j : Fin k) :
    Tendsto (fun n => blockDensity (G n c) (τ n) i j) atTop
      (𝓝 ((W c).toSymmKernel.rectIntegral (A i) (A j) /
        (μ.real (A i) * μ.real (A j)))) := by
  obtain ⟨d,hd⟩ := exists_positive_order_tail N hN
  apply (tendsto_add_atTop_iff_nat d).mp
  exact blockDensity_tendsto_rectIntegral (fun n => N (n+d)) hd
    (hN.comp (tendsto_add_atTop_nat d)) (fun n => G (n+d)) (fun n => τ (n+d))
    W A hA hpos (fun P => (htests P).comp (tendsto_add_atTop_nat d)) c i j

end ComponentTransfer.Realization
