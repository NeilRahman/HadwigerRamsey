import Mathlib

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A finite set can be distributed over any nonempty finite index type
with part sizes differing by at most one. Empty bins are allowed. -/
theorem exists_balanced_bins {I V : Type*} [Fintype I] [Nonempty I] [DecidableEq V]
    (R : Finset V) :
    ∃ D : I → Finset V, (∀ i, D i ⊆ R) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      (∀ v ∈ R, ∃ i, v ∈ D i) ∧
      ∀ i j, (D i).card ≤ (D j).card+1 := by
  classical
  by_cases hlarge : Fintype.card I ≤ R.card
  · obtain ⟨P,hP,hcard⟩ := Finpartition.exists_equipartition_card_eq R
      (Fintype.card_ne_zero) hlarge
    let e : I ≃ P.parts := Fintype.equivOfCardEq (by rw [Fintype.card_coe,hcard])
    refine ⟨fun i => (e i).val,?_,?_,?_,?_⟩
    · intro i
      exact P.le (e i).property
    · intro i j hij
      apply P.disjoint (e i).property (e j).property
      intro h
      exact hij (e.injective (Subtype.ext h))
    · intro v hv
      rw [← P.biUnion_parts] at hv
      obtain ⟨S,hS,hvS⟩ := mem_biUnion.mp hv
      refine ⟨e.symm ⟨S,hS⟩,?_⟩
      simpa using hvS
    · intro i j
      exact hP (e i).property (e j).property
  · let f : R ↪ I := Classical.choice (Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe]; omega))
    let D := fun i => (univ.filter (fun u : R => f u = i)).image Subtype.val
    have hmem : ∀ i v, v ∈ D i ↔ ∃ u : R, f u = i ∧ u.val = v := by
      intro i v
      simp [D]
    have hsmall : ∀ i, (D i).card ≤ 1 := by
      intro i
      apply card_le_one.mpr
      intro v hv w hw
      obtain ⟨u,hu,rfl⟩ := (hmem i v).mp hv
      obtain ⟨u',hu',rfl⟩ := (hmem i w).mp hw
      exact congrArg Subtype.val (f.injective (hu.trans hu'.symm))
    refine ⟨D,?_,?_,?_,?_⟩
    · intro i v hv
      obtain ⟨u,hu,rfl⟩ := (hmem i v).mp hv
      exact u.property
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨u,hu,huv⟩ := (hmem i v).mp hv
      obtain ⟨u',hu',huv'⟩ := (hmem j v).mp hw
      have huu : u = u' := Subtype.ext (huv.trans huv'.symm)
      exact hij (hu.symm.trans (huu ▸ hu'))
    · intro v hv
      exact ⟨f ⟨v,hv⟩,(hmem _ v).mpr ⟨⟨v,hv⟩,rfl,rfl⟩⟩
    · intro i j
      exact (hsmall i).trans (by omega)

/-- Extend disjoint equal-size cores to an equipartition of all vertices.
Only new vertices are distributed, so every original core is retained. -/
theorem extend_equal_cores {I V : Type*} [Fintype I] [Nonempty I] [Fintype V]
    [DecidableEq V] (C : I → Finset V) {L : ℕ}
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcard : ∀ i, (C i).card = L) :
    ∃ W : I → Finset V, (∀ i, C i ⊆ W i) ∧
      Pairwise (fun i j => Disjoint (W i) (W j)) ∧
      (∀ v, ∃ i, v ∈ W i) ∧
      ∀ i j, (W i).card ≤ (W j).card+1 := by
  classical
  let U := univ.biUnion C
  obtain ⟨D,hD,hDD,hcover,hbal⟩ := exists_balanced_bins (I := I) (univ \ U)
  have hCD : ∀ i j, Disjoint (C i) (D j) := by
    intro i j
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hh := (mem_sdiff.mp (hD j hw)).2
    exact hh (mem_biUnion.mpr ⟨i,mem_univ _,hv⟩)
  refine ⟨fun i => C i ∪ D i,?_,?_,?_,?_⟩
  · intro i
    exact subset_union_left
  · intro i j hij
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hdisj hij,hCD i j⟩,
      disjoint_union_right.mpr ⟨(hCD j i).symm,hDD hij⟩⟩
  · intro v
    by_cases hv : v ∈ U
    · obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
      exact ⟨i,mem_union_left _ hv⟩
    · obtain ⟨i,hi⟩ := hcover v (mem_sdiff.mpr ⟨mem_univ _,hv⟩)
      exact ⟨i,mem_union_right _ hi⟩
  · intro i j
    rw [card_union_of_disjoint (hCD i i),card_union_of_disjoint (hCD j j),hcard,hcard]
    have := hbal i j
    omega

end HadwigerRamsey.ThomasonUpper
