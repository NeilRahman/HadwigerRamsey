import ComponentTransfer.RealizationDensities
import ComponentTransfer.RealizationRestriction

open scoped BigOperators Topology Classical
open MeasureTheory Filter Finset Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

namespace ComponentTransfer.Realization

/-- A canonical numbering of a selected finite vertex set. -/
noncomputable def selectedEmbedding {n : ℕ} (S : Finset (Fin n)) : Fin S.card ↪ Fin n :=
  ⟨fun v => (S.equivFin.symm v).val, Subtype.val_injective.comp S.equivFin.symm.injective⟩

lemma selectedEmbedding_mem {n : ℕ} (S : Finset (Fin n)) (v : Fin S.card) :
    selectedEmbedding S v ∈ S := (S.equivFin.symm v).property

/-- The actual induced graph, renumbered by a finite initial segment. -/
noncomputable def selectedGraph {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin S.card) := G.comap (selectedEmbedding S)

/-- The selected graph is isomorphic to the usual induced graph on the
selected vertex subtype. -/
noncomputable def selectedGraphIso {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : selectedGraph G S ≃g G.induce (S : Set (Fin n)) where
  toEquiv := S.equivFin.symm
  map_rel_iff' := by intro x y; rfl

lemma finitePatternWeight_selected {r k n : ℕ} (P : Pattern r k)
    (G : Fin r → SimpleGraph (Fin n)) (S : Finset (Fin n))
    (f : Fin P.1 → Fin S.card) :
    finitePatternWeight P (fun c => selectedGraph (G c) S) f =
      finitePatternWeight P G (selectedEmbedding S ∘ f) := by
  simp only [finitePatternWeight, selectedGraph, Graphon.adjIndicator,
    SimpleGraph.comap_adj, Function.comp_apply]

lemma sum_selected_maps {n m : ℕ} (S : Finset (Fin n)) (F : (Fin m → Fin n) → ℝ) :
    (∑ f : Fin m → Fin S.card, F (selectedEmbedding S ∘ f)) =
      ∑ f : Fin m → Fin n with ∀ u, f u ∈ S, F f := by
  apply Finset.sum_bij (fun f _ => selectedEmbedding S ∘ f)
  · intro f _
    simp only [mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact fun u => selectedEmbedding_mem S (f u)
  · intro f _ g _ hfg
    funext u
    exact (selectedEmbedding S).injective (congrFun hfg u)
  · intro f hf
    have hmem := (mem_filter.mp hf).2
    refine ⟨fun u => S.equivFin ⟨f u,hmem u⟩, Finset.mem_univ _, ?_⟩
    funext u
    simp [selectedEmbedding]
  · intro f _
    rfl

lemma labelPattern_zero_of_ne {m n k : ℕ} (f : Fin m → Fin n)
    (a : Fin m → Fin k) (τ : Fin n → Fin k) (u : Fin m) (h : τ (f u) ≠ a u) :
    labelPattern f a τ = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ u)
  simp [labelIndicator,h]

lemma labelPattern_selected {r k n : ℕ} (P : Pattern r k)
    (τ : Fin n → Fin k) (B : Set (Fin k)) (f : Fin P.1 → Fin n) :
    (if ∀ u, τ (f u) ∈ B then labelPattern f P.label τ else 0) =
      if ∀ u, P.label u ∈ B then labelPattern f P.label τ else 0 := by
  by_cases hf : ∀ u, τ (f u) ∈ B <;> by_cases ha : ∀ u, P.label u ∈ B
  · simp [hf,ha]
  · simp only [if_pos hf, if_neg ha]
    push Not at ha
    obtain ⟨u,hu⟩ := ha
    apply labelPattern_zero_of_ne f P.label τ u
    intro heq
    exact hu (heq ▸ hf u)
  · simp only [if_neg hf, if_pos ha]
    push Not at hf
    obtain ⟨u,hu⟩ := hf
    symm
    apply labelPattern_zero_of_ne f P.label τ u
    intro heq
    exact hu (heq.symm ▸ ha u)
  · simp [hf,ha]

/-- Restriction to a union of marking classes has the precise finite-size
normalization, including the zero value for a test demanding an omitted class. -/
theorem finitePatternDensity_selected {r k n : ℕ} (hn : 0 < n)
    (P : Pattern r k) (G : Fin r → SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (B : Set (Fin k)) :
    let S := Finset.univ.filter (fun v => τ v ∈ B)
    finitePatternDensity P (fun c => selectedGraph (G c) S) (τ ∘ selectedEmbedding S) =
      if ∀ u, P.label u ∈ B then
        finitePatternDensity P G τ / ((S.card : ℝ)/(n : ℝ))^P.1 else 0 := by
  dsimp only
  let S := Finset.univ.filter (fun v => τ v ∈ B)
  have hsum : (∑ f : Fin P.1 → Fin S.card,
      finitePatternWeight P (fun c => selectedGraph (G c) S) f *
        labelPattern f P.label (τ ∘ selectedEmbedding S)) =
      if ∀ u, P.label u ∈ B then
        ∑ f : Fin P.1 → Fin n, finitePatternWeight P G f * labelPattern f P.label τ else 0 := by
    simp only [finitePatternWeight_selected]
    change (∑ f : Fin P.1 → Fin S.card,
      (fun g => finitePatternWeight P G g * labelPattern g P.label τ) (selectedEmbedding S ∘ f)) = _
    rw [sum_selected_maps S (fun g => finitePatternWeight P G g * labelPattern g P.label τ),
      Finset.sum_filter]
    have hterm (f : Fin P.1 → Fin n) :
        (if ∀ u, f u ∈ S then finitePatternWeight P G f * labelPattern f P.label τ else 0) =
        if ∀ u, P.label u ∈ B then finitePatternWeight P G f * labelPattern f P.label τ else 0 := by
      simp only [S, mem_filter, Finset.mem_univ, true_and]
      simpa only [mul_ite, mul_zero] using congrArg (fun z => finitePatternWeight P G f * z)
        (labelPattern_selected P τ B f)
    simp_rw [hterm]
    split_ifs <;> simp
  change _ / (S.card : ℝ)^P.1 = _
  rw [hsum]
  split_ifs with hvalid
  · unfold finitePatternDensity
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero _ hn')]
  · simp

lemma selected_mass_eq_sum {n k : ℕ} (τ : Fin n → Fin k) (B : Set (Fin k)) :
    ((Finset.univ.filter (fun v => τ v ∈ B)).card : ℝ) / (n : ℝ) =
      ∑ i ∈ B.toFinset, classMass τ i := by
  calc
    _ = (∑ v : Fin n, if τ v ∈ B then (1 : ℝ) else 0) / (n : ℝ) := by
      rw [Finset.sum_boole]
    _ = (∑ i : Fin k, ((Finset.univ.filter (fun v => τ v = i)).card : ℝ) *
        (if i ∈ B then (1 : ℝ) else 0)) / (n : ℝ) := by
      rw [sum_pullback τ (fun i => if i ∈ B then (1 : ℝ) else 0)]
    _ = ∑ i ∈ B.toFinset, classMass τ i := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_div, ite_div, zero_div]
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp

/-- The proportion of vertices in a union of marking classes converges to
its measure, including unions involving null refined classes. -/
theorem selected_mass_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r)
    (N : ℕ → ℕ) (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (π : α → Fin k) (hπ : Measurable π) (B : Set (Fin k))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W (fun i => π ⁻¹' {i})))) :
    Tendsto (fun n => ((Finset.univ.filter (fun v => τ n v ∈ B)).card : ℝ) / (N n : ℝ))
      atTop (𝓝 (μ.real (π ⁻¹' B))) := by
  have h := tendsto_finsetSum B.toFinset (fun i _ =>
    classMass_tendsto_of_patterns c N G τ W (fun i => π ⁻¹' {i})
      (fun i => hπ (measurableSet_singleton i)) htests i)
  simp_rw [← selected_mass_eq_sum] at h
  rw [sum_measureReal_preimage_singleton B.toFinset
    (fun i _ => hπ (measurableSet_singleton i))] at h
  simpa using h

theorem selected_card_tendsto {k : ℕ} (N : ℕ → ℕ)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (τ : ∀ n, Fin (N n) → Fin k) (B : Set (Fin k)) {a : ℝ} (ha : 0 < a)
    (hmass : Tendsto (fun n =>
      ((Finset.univ.filter (fun v => τ n v ∈ B)).card : ℝ) / (N n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => ((Finset.univ.filter (fun v => τ n v ∈ B)).card : ℝ)) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop.comp hN).atTop_mul_pos ha hmass
  apply h.congr'
  filter_upwards [] with n
  have hn : (N n : ℝ) ≠ 0 := by exact_mod_cast (hNpos n).ne'
  dsimp only [Function.comp_apply]
  field_simp

theorem selected_order_tendsto {k : ℕ} (N : ℕ → ℕ)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (τ : ∀ n, Fin (N n) → Fin k) (B : Set (Fin k)) {a : ℝ} (ha : 0 < a)
    (hmass : Tendsto (fun n =>
      ((Finset.univ.filter (fun v => τ n v ∈ B)).card : ℝ) / (N n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => (Finset.univ.filter (fun v => τ n v ∈ B)).card) atTop atTop :=
  tendsto_natCast_atTop_iff.mp (selected_card_tendsto N hNpos hN τ B ha hmass)

lemma markedDensity_inter_union {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (P : Pattern r k)
    (W : Fin r → Graphon α μ) (π : α → Fin k) (B : Set (Fin k)) :
    markedDensity P W (fun i => (π ⁻¹' B) ∩ (π ⁻¹' {i})) =
      if ∀ u, P.label u ∈ B then markedDensity P W (fun i => π ⁻¹' {i}) else 0 := by
  split_ifs with hvalid
  · unfold markedDensity
    congr 1
    funext x
    congr 1
    apply Finset.prod_congr rfl
    intro u _
    have hs : (π ⁻¹' B) ∩ (π ⁻¹' {P.label u}) = π ⁻¹' {P.label u} := by
      apply Set.inter_eq_right.mpr
      intro y hy
      change π y ∈ B
      exact (show π y = P.label u from hy).symm ▸ hvalid u
    dsimp only
    rw [hs]
  · push Not at hvalid
    obtain ⟨u,hu⟩ := hvalid
    apply markedDensity_zero_of_null P W _ u
    have hs : (π ⁻¹' B) ∩ (π ⁻¹' {P.label u}) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hu ((show π y = P.label u from hy.2) ▸ hy.1)
    rw [hs, measure_empty]

/-- Every marked test on the induced union converges on the normalized
restricted probability space. The induced graph has its actual selected order. -/
theorem selected_patterns_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r)
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (π : α → Fin k) (hπ : Measurable π) (B : Set (Fin k))
    (hpos : 0 < μ.real (π ⁻¹' B))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W (fun i => π ⁻¹' {i})))) :
    let S := fun n => Finset.univ.filter (fun v => τ n v ∈ B)
    ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (fun c => selectedGraph (G n c) (S n))
        (τ n ∘ selectedEmbedding (S n))) atTop
        (𝓝 (markedDensity P (fun c => restrictGraphon (W c) (π ⁻¹' B))
          (fun i => π ⁻¹' {i}))) := by
  dsimp only
  intro P
  have hm := selected_mass_tendsto c N G τ W π hπ B htests
  have hnonzero : μ (π ⁻¹' B) ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hpos
  rw [restrictGraphon_markedDensity P W (π ⁻¹' B)
    (hπ MeasurableSet.of_discrete) hnonzero, markedDensity_inter_union]
  by_cases hv : ∀ u, P.label u ∈ B
  · rw [if_pos hv]
    have h := (htests P).div (hm.pow P.1) (pow_ne_zero _ hpos.ne')
    apply h.congr'
    filter_upwards [] with n
    have heq := finitePatternDensity_selected (hNpos n) P (G n) (τ n) B
    simpa only [if_pos hv, Pi.div_apply] using heq.symm
  · rw [if_neg hv, zero_div]
    have heq (n : ℕ) := finitePatternDensity_selected (hNpos n) P (G n) (τ n) B
    simp only [if_neg hv] at heq
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Refining a marking does not change the selected union. This form gives
all refined tests on one fixed sequence of induced graphs. -/
theorem selected_patterns_tendsto_of_refinement {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {r k l : ℕ} (c : Fin r)
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (original : ∀ n, Fin (N n) → Fin k) (τ : ∀ n, Fin (N n) → Fin l)
    (W : Fin r → Graphon α μ) (π₀ : α → Fin k) (π : α → Fin l)
    (hπ : Measurable π) (forget : Fin l → Fin k)
    (hτ : ∀ n v, forget (τ n v) = original n v)
    (hrefine : ∀ x, forget (π x) = π₀ x) (B : Set (Fin k))
    (hpos : 0 < μ.real (π₀ ⁻¹' B))
    (htests : ∀ P : Pattern r l,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W (fun i => π ⁻¹' {i})))) :
    let S := fun n => Finset.univ.filter (fun v => original n v ∈ B)
    ∀ P : Pattern r l,
      Tendsto (fun n => finitePatternDensity P (fun c => selectedGraph (G n c) (S n))
        (τ n ∘ selectedEmbedding (S n))) atTop
        (𝓝 (markedDensity P (fun c => restrictGraphon (W c) (π₀ ⁻¹' B))
          (fun i => π ⁻¹' {i}))) := by
  have hA : π ⁻¹' (forget ⁻¹' B) = π₀ ⁻¹' B := by
    ext x
    simp only [Set.mem_preimage, hrefine]
  have hS : (fun n => Finset.univ.filter (fun v => τ n v ∈ forget ⁻¹' B)) =
      (fun n => Finset.univ.filter (fun v => original n v ∈ B)) := by
    funext n
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage, hτ]
  have h := selected_patterns_tendsto c N hNpos G τ W π hπ (forget ⁻¹' B)
    (by simpa only [hA] using hpos) htests
  change (∀ P, Tendsto (fun n => finitePatternDensity P
    (fun c => selectedGraph (G n c)
      ((fun n => Finset.univ.filter (fun v => τ n v ∈ forget ⁻¹' B)) n))
    (τ n ∘ selectedEmbedding
      ((fun n => Finset.univ.filter (fun v => τ n v ∈ forget ⁻¹' B)) n))) atTop
    (𝓝 (markedDensity P (fun c => restrictGraphon (W c) (π ⁻¹' (forget ⁻¹' B)))
      (fun i => π ⁻¹' {i})))) at h
  rw [hS,hA] at h
  exact h

/-- Selected orders diverge without conditions on finitely many initial orders. -/
theorem selected_order_tendsto_of_order_tendsto {k : ℕ} (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (τ : ∀ n, Fin (N n) → Fin k) (B : Set (Fin k)) {a : ℝ} (ha : 0 < a)
    (hmass : Tendsto (fun n =>
      ((Finset.univ.filter (fun v => τ n v ∈ B)).card : ℝ) / (N n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n => (Finset.univ.filter (fun v => τ n v ∈ B)).card) atTop atTop := by
  obtain ⟨d,hd⟩ := exists_positive_order_tail N hN
  apply (tendsto_add_atTop_iff_nat d).mp
  exact selected_order_tendsto (fun n => N (n+d)) hd
    (hN.comp (tendsto_add_atTop_nat d)) (fun n => τ (n+d)) B ha
    (hmass.comp (tendsto_add_atTop_nat d))

/-- Marked induced convergence needs only diverging source orders. -/
theorem selected_patterns_tendsto_of_order_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ} (c : Fin r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (π : α → Fin k) (hπ : Measurable π) (B : Set (Fin k))
    (hpos : 0 < μ.real (π ⁻¹' B))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W (fun i => π ⁻¹' {i})))) :
    let S := fun n => Finset.univ.filter (fun v => τ n v ∈ B)
    ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (fun c => selectedGraph (G n c) (S n))
        (τ n ∘ selectedEmbedding (S n))) atTop
        (𝓝 (markedDensity P (fun c => restrictGraphon (W c) (π ⁻¹' B))
          (fun i => π ⁻¹' {i}))) := by
  dsimp only
  intro P
  obtain ⟨d,hd⟩ := exists_positive_order_tail N hN
  apply (tendsto_add_atTop_iff_nat d).mp
  exact selected_patterns_tendsto c (fun n => N (n+d)) hd
    (fun n => G (n+d)) (fun n => τ (n+d)) W π hπ B hpos
    (fun P => (htests P).comp (tendsto_add_atTop_nat d)) P

/-- Every refined marking gives tests on the same induced union, allowing
initial zero orders in the source sequence. -/
theorem selected_patterns_tendsto_of_refinement_of_order_tendsto
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {r k l : ℕ} (c : Fin r)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (original : ∀ n, Fin (N n) → Fin k) (τ : ∀ n, Fin (N n) → Fin l)
    (W : Fin r → Graphon α μ) (π₀ : α → Fin k) (π : α → Fin l)
    (hπ : Measurable π) (forget : Fin l → Fin k)
    (hτ : ∀ n v, forget (τ n v) = original n v)
    (hrefine : ∀ x, forget (π x) = π₀ x) (B : Set (Fin k))
    (hpos : 0 < μ.real (π₀ ⁻¹' B))
    (htests : ∀ P : Pattern r l,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W (fun i => π ⁻¹' {i})))) :
    let S := fun n => Finset.univ.filter (fun v => original n v ∈ B)
    ∀ P : Pattern r l,
      Tendsto (fun n => finitePatternDensity P (fun c => selectedGraph (G n c) (S n))
        (τ n ∘ selectedEmbedding (S n))) atTop
        (𝓝 (markedDensity P (fun c => restrictGraphon (W c) (π₀ ⁻¹' B))
          (fun i => π ⁻¹' {i}))) := by
  dsimp only
  intro P
  obtain ⟨d,hd⟩ := exists_positive_order_tail N hN
  apply (tendsto_add_atTop_iff_nat d).mp
  exact selected_patterns_tendsto_of_refinement c (fun n => N (n+d)) hd
    (fun n => G (n+d)) (fun n => original (n+d)) (fun n => τ (n+d))
    W π₀ π hπ forget (fun n => hτ (n+d)) hrefine B hpos
    (fun P => (htests P).comp (tendsto_add_atTop_nat d)) P

end ComponentTransfer.Realization
