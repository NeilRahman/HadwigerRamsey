import HadwigerRamsey.ThomasonUpper.PermutationPairs

open scoped BigOperators Classical
open Finset

namespace HadwigerRamsey.ThomasonUpper

/-- A part of the random partition: one vertex at the same position in
every independently permuted block. -/
noncomputable def blockPart {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) (t : Fin s) : Finset V :=
  univ.image (fun i => e (i,p i t))

theorem mem_blockPart_iff {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) (t : Fin s) (v : V) :
    v ∈ blockPart e p t ↔ ∃ i, e (i,p i t) = v := by
  simp [blockPart]

/-- Every part has exactly one vertex per block. -/
theorem blockPart_card {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) (t : Fin s) :
    (blockPart e p t).card = Fintype.card I := by
  classical
  rw [blockPart,card_image_of_injective,card_univ]
  intro i j h
  exact congrArg Prod.fst (e.injective h)

/-- Different positions give disjoint parts because each block ordering
is a permutation and different blocks have disjoint vertex sets. -/
theorem blockPart_disjoint {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) {t u : Fin s} (htu : t ≠ u) :
    Disjoint (blockPart e p t) (blockPart e p u) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨i,hi⟩ := (mem_blockPart_iff e p t v).mp hv
  obtain ⟨j,hj⟩ := (mem_blockPart_iff e p u v).mp hw
  have hh := e.injective (hi.trans hj.symm)
  have hij : i = j := congrArg Prod.fst hh
  subst j
  exact htu ((p i).injective (congrArg Prod.snd hh))

/-- All vertices occur: find the block and position of a vertex, then
invert its block permutation. -/
theorem exists_mem_blockPart {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) (v : V) :
    ∃ t, v ∈ blockPart e p t := by
  obtain ⟨⟨i,x⟩,h⟩ := e.surjective v
  refine ⟨(p i).symm x,(mem_blockPart_iff e p _ v).mpr ⟨i,?_⟩⟩
  simpa using h

/-- Thus the parts form an exact equal-size partition of the vertex set. -/
theorem blockPart_cover {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] {s : ℕ} (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) :
    univ.biUnion (blockPart e p) = univ := by
  classical
  ext v
  simp only [mem_biUnion,mem_univ,true_and,iff_true]
  exact exists_mem_blockPart e p v

/-- The event that a part lies in a set factors into one event per block. -/
theorem blockPart_subset_iff {I V : Type*} [Fintype I] [DecidableEq V] {s : ℕ}
    (e : I × Fin s ≃ V) (p : I → Equiv.Perm (Fin s)) (t : Fin s) (S : Finset V) :
    blockPart e p t ⊆ S ↔ ∀ i, e (i,p i t) ∈ S := by
  constructor
  · intro h i
    exact h ((mem_blockPart_iff e p t _).mpr ⟨i,rfl⟩)
  · intro h v hv
    obtain ⟨i,rfl⟩ := (mem_blockPart_iff e p t v).mp hv
    exact h i

end HadwigerRamsey.ThomasonUpper
