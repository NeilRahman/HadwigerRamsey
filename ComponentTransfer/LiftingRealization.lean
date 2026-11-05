import ComponentTransfer.RealizationLemma

open scoped Classical Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open HadwigerRamsey HadwigerRamsey.ThomasonUpper

set_option backward.isDefEq.respectTransparency false

namespace ComponentTransfer.Realization

/-- A measurable mark retaining the prescribed disjoint sets and the ambient
set. The two additional classes are allowed to have measure zero. -/
theorem exists_lifting_mark {α : Type*} [MeasurableSpace α] {k : ℕ}
    (S : Set α) (hS : MeasurableSet S) (A : Fin k → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i, A i ⊆ S) :
    ∃ mark : α → Fin (k+2), Measurable mark ∧
      (∀ i, mark ⁻¹' {Fin.castAdd 2 i} = A i) ∧
      mark ⁻¹' {j | j.val ≤ k} = S := by
  let mark : α → Fin (k+2) := fun x =>
    if h : ∃ i, x ∈ A i then Fin.castAdd 2 h.choose
    else if x ∈ S then ⟨k, by omega⟩ else ⟨k+1, by omega⟩
  have hfibre (i : Fin k) : mark ⁻¹' {Fin.castAdd 2 i} = A i := by
    ext x
    change mark x = Fin.castAdd 2 i ↔ x ∈ A i
    dsimp only [mark]
    split_ifs with hx hSx
    · have hm := hx.choose_spec
      constructor
      · intro he
        have he' : hx.choose = i := Fin.ext (congrArg (fun z : Fin (k+2) => z.val) he)
        rwa [← he']
      · intro hxi
        have he : hx.choose = i := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisjoint hne) hm hxi
        rw [he]
    · constructor
      · intro he
        have hi := i.isLt
        have he' := congrArg Fin.val he
        dsimp at he'
        omega
      · intro hxi
        exact (hx ⟨i,hxi⟩).elim
    · constructor
      · intro he
        have hi := i.isLt
        have he' := congrArg Fin.val he
        dsimp at he'
        omega
      · intro hxi
        exact (hx ⟨i,hxi⟩).elim
  have hinner : mark ⁻¹' {j | j.val ≤ k} = S := by
    ext x
    change (mark x).val ≤ k ↔ x ∈ S
    dsimp only [mark]
    split_ifs with hx hSx
    · exact ⟨fun _ => hsub _ hx.choose_spec, fun _ => by exact (hx.choose.isLt).le⟩
    · simp [hSx]
    · simp [hSx]
  have hlast : mark ⁻¹' {⟨k+1, by omega⟩} = Sᶜ := by
    ext x
    change mark x = ⟨k+1, by omega⟩ ↔ x ∈ Sᶜ
    dsimp only [mark]
    split_ifs with hx hSx
    · have hm := hsub _ hx.choose_spec
      have hn : Fin.castAdd 2 hx.choose ≠ (⟨k+1, by omega⟩ : Fin (k+2)) := by
        intro he
        have he' := congrArg Fin.val he
        have hi := hx.choose.isLt
        dsimp at he'
        omega
      simp [hn, hm]
    · simp [hSx, Fin.ext_iff]
    · simp [hSx]
  have hmiddle : mark ⁻¹' {⟨k, by omega⟩} = S \ ⋃ i, A i := by
    ext x
    change mark x = ⟨k, by omega⟩ ↔ x ∈ S \ ⋃ i, A i
    dsimp only [mark]
    split_ifs with hx hSx
    · have hn : Fin.castAdd 2 hx.choose ≠ (⟨k, by omega⟩ : Fin (k+2)) := by
        intro he
        have he' := congrArg Fin.val he
        have hi := hx.choose.isLt
        dsimp at he'
        omega
      simp [hn, Set.mem_iUnion, hx]
    · simp [hSx, Set.mem_iUnion, hx]
    · simp [hSx]
  refine ⟨mark, ?_, hfibre, hinner⟩
  apply measurable_to_countable'
  intro j
  by_cases hj : j.val < k
  · have he : j = Fin.castAdd 2 (⟨j.val,hj⟩ : Fin k) := by ext; rfl
    rw [he,hfibre]
    exact hA _
  · by_cases he : j.val = k
    · have he' : j = ⟨k, by omega⟩ := Fin.ext he
      rw [he',hmiddle]
      exact hS.diff (MeasurableSet.iUnion hA)
    · have he' : j = ⟨k+1, by omega⟩ := by apply Fin.ext; change j.val = k+1; have := j.isLt; omega
      rw [he',hlast]
      exact hS.compl

/-- The ordinary density of two positive-mass marking classes converges even
when other marking classes are null. -/
theorem blockDensity_tendsto_positive_classes
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {r k : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (G : ∀ n, Fin r → SimpleGraph (Fin (N n)))
    (τ : ∀ n, Fin (N n) → Fin k) (W : Fin r → Graphon α μ)
    (A : Fin k → Set α) (hA : ∀ i, MeasurableSet (A i))
    (htests : ∀ P : Pattern r k,
      Tendsto (fun n => finitePatternDensity P (G n) (τ n)) atTop
        (𝓝 (markedDensity P W A))) (c : Fin r) (i j : Fin k)
    (hi : 0 < μ.real (A i)) (hj : 0 < μ.real (A j)) :
    Tendsto (fun n => blockDensity (G n c) (τ n) i j) atTop
      (𝓝 ((W c).toSymmKernel.rectIntegral (A i) (A j) /
        (μ.real (A i) * μ.real (A j)))) := by
  have hm (i : Fin k) := classMass_tendsto_of_patterns c N G τ W A hA htests i
  have hsi := classVertices_card_tendsto_of_order_tendsto N hN τ i hi (hm i)
  have hsj := classVertices_card_tendsto_of_order_tendsto N hN τ j hj (hm j)
  have he := htests (edgePattern c i j)
  simp only [finitePatternDensity_edge, markedDensity_edge] at he
  rw [indicator_rectangle_integral μ _ _ (hA i) (hA j)] at he
  have hNpos := hN.eventually_gt_atTop 0
  by_cases hij : i = j
  · subst j
    have hinv : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp hN)
    have hd := (hm i).mul ((hm i).sub hinv)
    simp only [sub_zero] at hd
    have h := he.div hd (mul_ne_zero hi.ne' hi.ne')
    apply h.congr'
    filter_upwards [hsi.eventually_ge_atTop 2, hNpos] with n hn hpos
    have hn' : 2 ≤ (classVertices (τ n) i).card := by exact_mod_cast hn
    simp only [blockDensity, ite_true]
    exact (internalDensity_eq_normalized_interedges hpos (G n c) (τ n) i hn').symm
  · have h := he.div ((hm i).mul (hm j)) (mul_ne_zero hi.ne' hj.ne')
    apply h.congr'
    filter_upwards [hsi.eventually_ge_atTop 1, hsj.eventually_ge_atTop 1, hNpos] with n hni hnj hpos
    have hi' : 0 < (classVertices (τ n) i).card := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hni)
    have hj' : 0 < (classVertices (τ n) j).card := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hnj)
    simp only [blockDensity, if_neg hij]
    exact (edgeDensity_eq_normalized_interedges hpos (G n c) (τ n) i j hi' hj').symm

end ComponentTransfer.Realization
