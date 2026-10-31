import HadwigerRamsey.ThomasonUpper.Density

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- Select an exact integer number of edges in every fiber of an edge
classification, producing a spanning subgraph of the original graph. -/
theorem exists_subgraph_with_edge_counts {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I] (G : SimpleGraph V) (f : Sym2 V → I)
    (b : I → ℕ) (hb : ∀ i, b i ≤ (G.edgeFinset.filter fun e => f e = i).card) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      ∀ i, (H.edgeFinset.filter fun e => f e = i).card = b i := by
  classical
  choose S hS hcard using fun i => exists_subset_card_eq (hb i)
  let E := univ.biUnion S
  have hEG : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
    exact (mem_filter.mp (hS i hi)).1
  let H := G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 V)) : Set (Sym2 V))
  letI : DecidableRel H.Adj := Classical.decRel _
  have hHE : H.edgeFinset = E := by
    ext e
    have heG : e ∈ E → e ∈ G.edgeSet := fun h => by simpa using hEG h
    simp only [SimpleGraph.mem_edgeFinset, H, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, mem_coe, mem_sdiff]
    tauto
  refine ⟨H, G.deleteEdges_le _, ?_⟩
  intro i
  have heq : E.filter (fun e => f e = i) = S i := by
    ext e
    constructor
    · intro he
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp (mem_filter.mp he).1
      have hji : j = i := ((mem_filter.mp (hS j hj)).2).symm.trans (mem_filter.mp he).2
      simpa only [hji] using hj
    · intro he
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,he⟩, (mem_filter.mp (hS i he)).2⟩
  exact (congrArg (fun F : Finset (Sym2 V) => (F.filter fun e => f e = i).card) hHE).trans
    ((congrArg Finset.card heq).trans (hcard i))

/-- The edge fiber belonging to an unordered pair of vertex classes. -/
noncomputable def blockEdges {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => Sym2.map τ e = s(i,j)

theorem blockEdges_card_offdiag {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {i j : Fin k} (hij : i ≠ j) :
    (blockEdges G τ i j).card = (G.interedges (classVertices τ i) (classVertices τ j)).card := by
  classical
  symm
  apply card_bij (fun e _ => s(e.1,e.2))
  · intro e he
    obtain ⟨hx,hy,hxy⟩ := G.mem_interedges_iff.mp he
    refine mem_filter.mpr ⟨by simpa using hxy, ?_⟩
    simp only [Sym2.map_mk, (mem_filter.mp hx).2, (mem_filter.mp hy).2]
  · intro e he f hf hef
    obtain ⟨hx,hy,_⟩ := G.mem_interedges_iff.mp he
    obtain ⟨hu,hv,_⟩ := G.mem_interedges_iff.mp hf
    rcases Sym2.eq_iff.mp hef with h | h
    · exact Prod.ext h.1 h.2
    · have hh := congrArg τ h.1
      exact False.elim (hij (by simpa only [(mem_filter.mp hx).2, (mem_filter.mp hv).2] using hh))
  · intro e he
    obtain ⟨heG,heτ⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using heG
      rcases Sym2.eq_iff.mp heτ with h | h
      · exact ⟨(u,v), G.mem_interedges_iff.mpr
          ⟨by simp [classVertices,h.1], by simp [classVertices,h.2],huv⟩,rfl⟩
      · exact ⟨(v,u), G.mem_interedges_iff.mpr
          ⟨by simp [classVertices,h.2], by simp [classVertices,h.1],huv.symm⟩, by simp [Sym2.eq_swap]⟩

theorem blockEdges_card_diag {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i : Fin k) :
    (blockEdges G τ i i).card = (G.induce (classVertices τ i : Set (Fin n))).edgeFinset.card := by
  classical
  symm
  apply card_bij (fun e _ => Sym2.map Subtype.val e)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u.val v.val := by simpa using he
      refine mem_filter.mpr ⟨by simpa using huv, ?_⟩
      have hu := (mem_filter.mp u.property).2
      have hv := (mem_filter.mp v.property).2
      simp only [Sym2.map_mk, hu, hv]
  · intro e _ f _ hef
    exact Sym2.map.injective Subtype.val_injective hef
  · intro e he
    obtain ⟨heG,heτ⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using heG
      have hpair : τ u = i ∧ τ v = i := by simpa only [Sym2.map_mk,Sym2.eq_iff,or_self] using heτ
      have hu : u ∈ classVertices τ i := by simp [classVertices,hpair.1]
      have hv : v ∈ classVertices τ i := by simp [classVertices,hpair.2]
      exact ⟨s(⟨u,hu⟩,⟨v,hv⟩), by simpa using huv, rfl⟩

def blockCapacity {n k : ℕ} (τ : Fin n → Fin k) (i j : Fin k) : ℕ :=
  if i = j then (classVertices τ i).card.choose 2
  else (classVertices τ i).card * (classVertices τ j).card

theorem blockCapacity_symm {n k : ℕ} (τ : Fin n → Fin k) (i j : Fin k) :
    blockCapacity τ i j = blockCapacity τ j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp [blockCapacity,h,Ne.symm h,Nat.mul_comm]

theorem blockEdges_card_le_capacity {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) : (blockEdges G τ i j).card ≤ blockCapacity τ i j := by
  classical
  by_cases h : i = j
  · subst j
    rw [blockEdges_card_diag]
    simpa [blockCapacity] using (G.induce (classVertices τ i : Set (Fin n))).card_edgeFinset_le_card_choose_two
  · rw [blockEdges_card_offdiag G τ h]
    simpa only [blockCapacity,if_neg h] using G.card_interedges_le_mul (classVertices τ i) (classVertices τ j)

theorem blockDensity_eq_blockEdges {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) :
    blockDensity G τ i j = (blockEdges G τ i j).card / (blockCapacity τ i j : ℝ) := by
  classical
  by_cases h : i = j
  · subst j
    simp [blockDensity, blockCapacity, blockEdges_card_diag, internalDensity]
  · simp only [blockDensity,blockCapacity,if_neg h,blockEdges_card_offdiag G τ h,
      SimpleGraph.edgeDensity_def,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Nat.cast_mul]

theorem blockDensity_mul_capacity {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) (i j : Fin k) :
    blockDensity G τ i j * blockCapacity τ i j = (blockEdges G τ i j).card := by
  rw [blockDensity_eq_blockEdges]
  by_cases h : blockCapacity τ i j = 0
  · have he : (blockEdges G τ i j).card = 0 := by
      have hh := blockEdges_card_le_capacity G τ i j
      omega
    simp [h,he]
  · exact div_mul_cancel₀ _ (by exact_mod_cast h)

/-- The spanning subgraph H used in Theorem 1.5: select exactly the
floor of capped density times the number of possible pairs in each block. -/
theorem exists_capped_subgraph_counts {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧ ∀ i j,
      (blockEdges H τ i j).card = ⌊cappedDensity G τ ε i j * blockCapacity τ i j⌋₊ := by
  classical
  let b : Sym2 (Fin k) → ℕ := Sym2.lift ⟨
    fun i j => ⌊cappedDensity G τ ε i j * blockCapacity τ i j⌋₊,
    fun i j => by
      dsimp only
      rw [cappedDensity_symm G τ ε i j,blockCapacity_symm τ i j]⟩
  have hb : ∀ e : Sym2 (Fin k), b e ≤ (G.edgeFinset.filter fun f => Sym2.map τ f = e).card := by
    intro e
    induction e using Sym2.ind with
    | _ i j =>
      change ⌊cappedDensity G τ ε i j * blockCapacity τ i j⌋₊ ≤ (blockEdges G τ i j).card
      apply Nat.floor_le_of_le
      have hh := mul_le_mul_of_nonneg_right
        (min_le_left (blockDensity G τ i j) (1-ε)) (Nat.cast_nonneg (blockCapacity τ i j) : (0:ℝ) ≤ _)
      rw [blockDensity_mul_capacity] at hh
      exact hh
  obtain ⟨H,hHG,hH⟩ := exists_subgraph_with_edge_counts G (Sym2.map τ) b hb
  refine ⟨H,hHG,?_⟩
  intro i j
  exact hH s(i,j)

/-- The capped subgraph has the required density upper bound and the
exact reciprocal-denominator rounding error in every nondegenerate block. -/
theorem exists_capped_subgraph {n k : ℕ} (G : SimpleGraph (Fin n))
    (τ : Fin n → Fin k) {ε : ℝ} (hε : ε ≤ 1)
    (hsize : ∀ i, 2 ≤ (classVertices τ i).card) :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧ ∀ i j,
      blockDensity H τ i j ≤ cappedDensity G τ ε i j ∧
      |blockDensity H τ i j - cappedDensity G τ ε i j| < 1/(blockCapacity τ i j : ℝ) := by
  classical
  obtain ⟨H,hHG,hH⟩ := exists_capped_subgraph_counts G τ (ε := ε)
  refine ⟨H,hHG,?_⟩
  intro i j
  have hcap : 0 < blockCapacity τ i j := by
    by_cases h : i = j
    · subst j
      simpa [blockCapacity] using Nat.choose_pos (hsize i)
    · simpa only [blockCapacity,if_neg h] using
        Nat.mul_pos (by have := hsize i; omega : 0 < (classVertices τ i).card)
          (by have := hsize j; omega : 0 < (classVertices τ j).card)
  have hcapR : (0 : ℝ) < blockCapacity τ i j := by exact_mod_cast hcap
  have hx : 0 ≤ cappedDensity G τ ε i j * blockCapacity τ i j :=
    mul_nonneg (cappedDensity_bounds G τ hε i j).1 hcapR.le
  have hf := Nat.floor_le hx
  have hf' := Nat.lt_floor_add_one (cappedDensity G τ ε i j * blockCapacity τ i j)
  rw [blockDensity_eq_blockEdges,hH]
  have hh : (⌊cappedDensity G τ ε i j * blockCapacity τ i j⌋₊ : ℝ) /
      blockCapacity τ i j ≤ cappedDensity G τ ε i j := (div_le_iff₀ hcapR).mpr hf
  refine ⟨hh,?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hh)]
  apply (lt_div_iff₀ hcapR).mpr
  have he : -( (⌊cappedDensity G τ ε i j * blockCapacity τ i j⌋₊ : ℝ) /
      blockCapacity τ i j - cappedDensity G τ ε i j)*blockCapacity τ i j =
      cappedDensity G τ ε i j*blockCapacity τ i j - ⌊cappedDensity G τ ε i j * blockCapacity τ i j⌋₊ := by field_simp; ring
  rw [he]
  linarith

end HadwigerRamsey.ThomasonUpper
